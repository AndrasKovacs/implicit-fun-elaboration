-- {-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import Control.Exception
import Control.Monad
import Data.Maybe
import Lens.Micro.Platform
import qualified Data.IntMap as IM

import Types
import Evaluation
import ElabState
import Errors

-- import Pretty
-- import Debug.Trace

-- Context operations
--------------------------------------------------------------------------------

emptyCxt :: Cxt
emptyCxt = Cxt VNil TNil [] [] 0

-- | Add a bound variable.
bind :: Name -> Origin -> VTy -> StageExp -> Cxt -> Cxt
bind x o ~a s (Cxt vs tys ns no d) =
  Cxt (VSkip vs) (TBound tys a s) (x:ns) (o:no) (d + 1)

-- | Add a bound variable which comes from surface syntax.
bindSrc :: Name -> VTy -> StageExp -> Cxt -> Cxt
bindSrc x = bind x Source

-- | Define a new variable.
define :: Name -> VTy -> StageExp -> Val -> Cxt -> Cxt
define x ~a ~s ~t (Cxt vs tys ns no d) =
  Cxt (VDef vs t) (TDef tys a s) (x:ns) (Source:no) (d + 1)

-- | Lift ("skolemize") a value in an extended context to a function in a
--   non-extended context.
liftVal :: Cxt -> Val -> (Val -> Val)
liftVal cxt t = \ ~x -> eval (VDef (cxt^.vals) x) $ quote (cxt^.len+1) t


-- Unification
--------------------------------------------------------------------------------

-- | Checks that a spine consists only of distinct bound vars.
--   Returns a partial variable renaming on success, alongside the size
--   of the spine, and the list of variables in the spine.
--   May throw `SpineError`.
checkSp :: Spine -> IO (Renaming, Lvl, [Lvl])
checkSp = (over _3 reverse <$>) . go where
  go :: Spine -> IO (Renaming, Lvl, [Lvl])
  go = \case
    SNil          -> pure (mempty, 0, [])
    SApp sp u i o -> do
      (!r, !d, !xs) <- go sp
      case force u of
        VVar x | IM.member x r -> throwIO $ NonLinearSpine x
               | otherwise     -> pure (IM.insert x d r, d + 1, x:xs)
        _      -> throwIO SpineNonVar
    SProj1 _ -> throwIO SpineProjection
    SProj2 _ -> throwIO SpineProjection
    SDown _  -> throwIO SpineProjection

-- | Close a type in a cxt by wrapping it in Pi types and explicit strengthenings.
closingTy :: Cxt -> Ty -> Ty
closingTy cxt = go (cxt^.types) (cxt^.names) (cxt^.len) where
  go TNil                    []     d b = b
  go (TDef tys a s)          (x:ns) d b = go tys ns (d-1) (Skip b)
  go (TBound tys a _)        (x:ns) d b = go tys ns (d-1) (Pi x Expl (quote (d-1) a) b)
  go _                       _      _ _ = error "impossible"

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`, and the binder names from a list. If we run out of provided
--   binder names, we pick the names from the Pi domains.
closingTm :: (VTy, Int, [Name]) -> Tm -> Tm
closingTm = go 0 where
  getName []     x = x
  getName (x:xs) _ = x

  go d (a, 0, _)   rhs = rhs
  go d (a, len, xs) rhs = case force a of
    VPi (getName xs -> x) i a b ->
      Lam x i Source (quote d a)  $ go (d + 1) (b (VVar d), len-1, drop 1 xs) rhs
    _ -> error "impossible"

-- | Eta expand an unsolved meta. This causes all projections to disappear from
--   meta spines. An expansion is modulo the current metacontext; other meta
--   solutions may cause the type of a meta to accrue more negative types, and
--   may require re-expansion.
etaExpandMeta :: MId -> IO ()
etaExpandMeta m = do
  (a, s) <- lookupMeta m >>= \case
    Unsolved a s -> pure (a, s)
    _              -> error "impossible"

  let go :: Cxt -> VTy -> StageExp -> IO Tm
      go cxt a s = case force a of
        VPi x i a b ->
          Lam x i Source (quote (cxt^.len) a) <$> go (bindSrc x a s cxt) (b (VVar (cxt^.len))) s
        VRec VTEmpty ->
          pure Tempty
        VRec (VTCons x a b) -> do
          t <- go cxt a s
          u <- go cxt (b (eval (cxt^.vals) t)) s
          pure (Tcons t u)
        VCode a ->
          Up <$> go cxt a (vPred s)
        a ->
          freshMeta cxt a s

  t <- go emptyCxt a s
  unifyWhile emptyCxt (VNe (HMeta m) SNil) (eval VNil t) s


-- | Strengthens a value, returns a quoted normal result. This performs scope
--   checking, meta occurs checking and (recursive) pruning at the same time.
--   May throw `StrengtheningError`.
strengthen :: Str -> Val -> IO Tm
strengthen str = go where

  -- we only prune all-variable spines with illegal var occurrences,
  -- we don't prune illegal cyclic meta occurrences.
  prune :: MId -> Spine -> IO ()
  prune m sp = do

    let pruning :: Maybe [Bool]
        pruning = go [] sp where
          go acc SNil                    = pure acc
          go acc (SApp sp (VVar x) i _)  = go (isJust (IM.lookup x (str^.ren)) : acc) sp
          go _   _                       = Nothing

    case pruning of
      Nothing                    -> pure ()  -- spine is not a var substitution
      Just pruning | and pruning -> pure ()  -- no pruneable vars
      Just pruning               -> do

        (metaTy, metaS) <- lookupMeta m >>= \case
          Unsolved a s -> pure (a, s)
          _            -> error "impossible"

        -- note: this can cause recursive pruning of metas in types
        (prunedTy :: Ty) <- do
          let go :: [Bool] -> Str -> VTy -> IO Ty
              go [] str a = strengthen str a
              go (True:pr) str (force -> VPi x i a b) =
                Pi x i <$> strengthen str a <*> go pr (liftStr str) (b (VVar (str^.cod)))
              go (False:pr) str (force -> VPi x i a b) =
                go pr (skipStr str) (b (VVar (str^.cod)))
              go _ _ _ = error "impossible"

          go pruning (Str 0 0 mempty Nothing) metaTy

        m' <- newMeta $ Unsolved (eval VNil prunedTy) metaS

        let argNum = length pruning
            body = go pruning metaTy (Meta m') 0 where
              go [] a acc d = acc
              go (True:pr) (force -> VPi x i a b) acc d =
                go pr (b (VVar d)) (App acc (Var (argNum - d - 1)) i Source) (d + 1)
              go (False:pr) (force -> VPi x i a b) acc d =
                go pr (b (VVar d)) acc (d + 1)
              go _ _ _ _ = error "impossible"

        let rhs = closingTm (metaTy, argNum, []) body
        writeMeta m $ Solved (eval VNil rhs)

  go t = case force t of
    VNe (HVar x) sp  -> case IM.lookup x (str^.ren) of
                          Nothing -> throwIO $ ScopeError x
                          Just x' -> goSp (Var (str^.dom - x' - 1)) sp
    VNe (HMeta m) sp -> if Just m == str^.occ then
                          throwIO OccursCheck
                        else do
                          prune m sp
                          case force (VNe (HMeta m) sp) of
                            VNe (HMeta m) sp -> goSp (Meta m) sp
                            _                -> error "impossible"

    VPi x i a b      -> Pi x i <$> go a <*> goBind b
    VLam x i o a t   -> Lam x i o <$> go a <*> goBind t
    VU s             -> pure (U (vStage s))
    VTel s           -> pure (Tel (vStage s))
    VRec a           -> Rec <$> go a
    VTEmpty          -> pure TEmpty
    VTCons x a b     -> TCons x <$> go a <*> goBind b
    VTempty          -> pure Tempty
    VTcons t u       -> Tcons <$> go t <*> go u
    VCode a          -> Code <$> go a
    VUp t            -> Up <$> go t

  goBind t = strengthen (liftStr str) (t (VVar (str^.cod)))

  goSp h = \case
    SNil           -> pure h
    SApp sp u i o  -> App <$> goSp h sp <*> go u <*> pure i <*> pure o
    SProj1 sp      -> Proj1 <$> goSp h sp
    SProj2 sp      -> Proj2 <$> goSp h sp
    SDown sp       -> Down <$> goSp h sp

-- | May throw `UnifyError`.
solveMeta :: Cxt -> MId -> Spine -> Val -> StageExp -> IO ()
solveMeta cxt m sp rhs s = do

  -- these normal forms are only used in error reporting
  let ~topLhs = quote (cxt^.len) (VNe (HMeta m) sp)
      ~topRhs = quote (cxt^.len) rhs

  try (checkSp sp) >>= \case
    Left SpineProjection -> do
      etaExpandMeta m
      unify cxt (VNe (HMeta m) sp) rhs s
    Left e ->
      throwIO $ SpineError cxt topLhs topRhs e
    Right (ren, spLen, spVars) -> do

      --  strengthen right hand side
      rhs <- strengthen (Str spLen (cxt^.len) ren (Just m)) rhs
             `catch` (throwIO . StrengtheningError cxt topLhs topRhs)

      metaTy <- lookupMeta m >>= \case
        Unsolved a _ -> pure a
        _            -> error "impossible"

      let spVarNames = map (lvlName cxt) spVars
      let closedRhs = closingTm (metaTy, spLen, spVarNames) rhs
      writeMeta m (Solved (eval VNil closedRhs))


-- | Create a fresh stage metavariable.
freshStage :: IO StageExp
freshStage = SVar <$> newStageVar Nothing

-- | Create a fresh meta with given type, return
--   the meta applied to all bound variables.
freshMeta :: Cxt -> VTy -> StageExp -> IO Tm
freshMeta cxt (quote (cxt^.len) -> a) topS = do
  let metaTy = closingTy cxt a
  m <- newMeta $ Unsolved (eval VNil metaTy) topS

  let vars :: Types -> (Spine, Lvl)
      vars TNil                            = (SNil, 0)
      vars (TDef (vars -> (sp, !d)) _ _)   = (sp, d + 1)
      vars (TBound (vars -> (sp, !d)) _ _) = (SApp sp (VVar d) Expl Source, d + 1)

  let sp = fst $ vars (cxt^.types)
  pure (quote (cxt^.len) (VNe (HMeta m) sp))

-- | Wrap the inner `UnifyError` arising from unification in an `UnifyErrorWhile`.
--   This decorates an error with one additional piece of context.
unifyWhile :: Dbg => Cxt -> Val -> Val -> StageExp -> IO ()
unifyWhile cxt l r s =
  unify cxt l r s
  `catch`
  (report cxt . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))


solveStage :: Dbg => StageId -> StageExp -> IO ()
solveStage x s@(StageExp h n) = do
  -- occurs check
  case h of
    SHVar x' | x == x' -> report emptyCxt $ StageError (SVar x) s
    _                  -> pure ()
  modifyStageVar x $ maybe (Just s) (error "impossible")

unifyStage :: Dbg => StageExp -> StageExp -> IO ()
unifyStage s s' = go (vStage s) (vStage s') where
  go (SVar x) (SVar x') | x == x' = pure ()
  go (SSuc s) (SSuc s')           = go s s'
  go SZero    SZero               = pure ()
  go (SVar x) s'                  = solveStage x s'
  go s        (SVar x')           = solveStage x' s
  go s        s'                  = report emptyCxt $ StageError s s'

-- | May throw `UnifyError`.
unify :: Dbg => Cxt -> Val -> Val -> StageExp -> IO ()
unify cxt l r topS = go l r where

  unifyError =
    throwIO $ UnifyError cxt (quote (cxt^.len) l) (quote (cxt^.len) r)

  -- if both sides are meta-headed, we simply try to check both spines
  flexFlex m sp m' sp' = do
    try @SpineError (checkSp sp) >>= \case
      Left{}  -> solveMeta cxt m' sp' (VNe (HMeta m) sp) topS
      Right{} -> solveMeta cxt m sp (VNe (HMeta m') sp') topS

  go t t' = do
   -- traceM "unify"
   -- traceM (showVal cxt (force t))
   -- traceM (showVal cxt (force t'))
   -- traceShowM (vStage topS)
   case (force t, force t') of
    (VLam x _ o a t, VLam _ _ _ _ t')        -> goBind x a t t'
    (VLam x i o a t, t')                     -> goBind x a t (\ ~v -> vApp t' v i o)
    (t, VLam x' i' o' a' t')                 -> goBind x' a' (\ ~v -> vApp t v i' o') t'
    (VPi x i a b, VPi x' i' a' b') | i == i' -> go a a' >> goBind x a b b'
    (VU s, VU s')                            -> unifyStage s s'
    (VTel _, VTel _)                         -> pure ()
    (VRec a, VRec a')                        -> go a a'
    (VTEmpty, VTEmpty)                       -> pure ()
    (VTCons x a b, VTCons x' a' b')          -> go a a' >> goBind x a b b'
    (VTempty, _)                             -> pure ()
    (_, VTempty)                             -> pure ()
    (VTcons t u, VTcons t' u')               -> go t t' >> go u u'
    (VTcons t u, t')                         -> go t (vProj1 t') >> go u (vProj2 t')
    (t, VTcons t' u')                        -> go (vProj1 t) t' >> go (vProj2 t) u'

    (VCode a, VCode a')                      -> unify cxt a a' (vPred topS)
    (VUp t, VUp t')                          -> unify cxt t t' (vPred topS)

    (VNe h sp, VNe h' sp') | h == h'         -> goSp sp sp' topS
    (VNe (HMeta m) sp, VNe (HMeta m') sp')   -> flexFlex m sp m' sp'
    (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t' topS
    (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t topS

    _                 -> unifyError

  goBind x a t t' =
    let v = VVar (cxt^.len) in unify (bindSrc x a topS cxt) (t v) (t' v) topS

  goSp sp sp' s = case (sp, sp') of
    (SNil, SNil)                            -> pure ()
    (SApp sp u i o, SApp sp' u' i' o') | i == i' -> goSp sp sp' s >> unify cxt u u' s
    (SDown sp, SDown sp')                   -> goSp sp sp' (SSuc s)
    (SProj1 sp, SProj1 sp')                 -> goSp sp sp' s
    (SProj2 sp, SProj2 sp')                 -> goSp sp sp' s
    _                                       -> error "impossible"


-- Elaboration
--------------------------------------------------------------------------------

-- | Insert fresh implicit applications.
insert' :: Dbg => Cxt -> IO (Tm, VTy, StageExp) -> IO (Tm, VTy, StageExp)
insert' cxt act = do
  (t, va, s) <- act
  let go t va = case force va of
        VPi x Impl a b -> do
          m <- freshMeta cxt a s
          let mv = eval (cxt^.vals) m
          go (App t m Impl Inserted) (b mv)
        va -> pure (t, va, s)
  go t va

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Dbg => Cxt -> IO (Tm, VTy, StageExp) -> IO (Tm, VTy, StageExp)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _ _ _), va, s) -> pure (t, va, s)
  res                           -> insert' cxt (pure res)

inferU :: Dbg => Cxt -> Raw -> IO (Tm, StageExp)
inferU cxt t = do
  (t, a, s) <- infer cxt t
  unifyWhile cxt a (VU s) s
  pure (t, s)

nTimes :: Int -> (a -> a) -> (a -> a)
nTimes n f ~a | n <= 0 = a
nTimes n f ~a = nTimes (n - 1) f (f a)

coerce :: Dbg => Cxt -> Tm -> VTy -> StageExp -> VTy -> StageExp -> IO Tm
coerce cxt t a s a' s' = maybe t id <$> go cxt t a s a' s' where

  justUnify :: Dbg => Cxt -> VTy -> StageExp -> VTy -> StageExp -> IO (Maybe Tm)
  justUnify cxt a s a' s' = do
    unifyStage s s'
    unifyWhile cxt a a' s
    pure Nothing

  goFlex :: Dbg => Cxt -> Tm -> VTy -> StageExp -> VTy -> StageExp -> IO (Maybe Tm)
  goFlex cxt t a (vStage -> s) a' (vStage -> s') = case (s, s') of

    (StageExp h n, StageExp h' n') | h == h' -> case compare n n' of
      EQ -> do
        unifyWhile cxt a a' s
        pure Nothing

      -- lift lhs to level of rhs
      LT -> do
        let diff = n' - n
            upt  = nTimes diff Up t
            upa  = nTimes diff VCode a
        unifyWhile cxt upa a' s'
        pure $ Just upt

      -- lower lhs to level of rhs
      GT -> do
        let diff = n - n'
        m <- eval (cxt^.vals) <$> freshMeta cxt (VU s') s'
        let upm   = nTimes diff VCode m
            downt = nTimes diff Down t
        unifyWhile cxt a upm s
        unifyWhile cxt m a' s'
        pure $ Just downt

    _ -> justUnify cxt a s a' s'

  go :: Dbg => Cxt -> Tm -> VTy -> StageExp -> VTy -> StageExp -> IO (Maybe Tm)
  go cxt t a s a' s' = do
   -- traceM "coe"
   -- traceM $ showVal cxt a
   -- traceShowM s
   -- traceM $ showVal cxt a'
   -- traceShowM s'
   case (force a, force a') of
    (VCode a, VCode a') ->
      (Up <$>) <$> go cxt (Down t) a (vPred s) a' (vPred s')

    (VPi x i a b, VPi x' i' a' b') -> do
      when (i /= i') $ report cxt $ IcitMismatch i i'
      let cxt' = bind x Source a' s' cxt
      coev0 <- go cxt' (Var 0) a' s' a s
      case coev0 of
        Nothing -> do
          body <- go cxt' (App (Wk t) (Var 0) i Source)
                          (b (eval (cxt'^.vals) (Var 0))) s
                          (b' (VVar (cxt^.len))) s'
          pure $ Lam x i Source (quote (cxt^.len) a') <$> body
        Just coev0 -> do
          body <- go cxt' (App (Wk t) coev0 i Source)
                          (b (eval (cxt'^.vals) coev0)) s
                          (b' (VVar (cxt^.len))) s'
          case body of
            Nothing ->
              pure $ Just $ Lam x i Source (quote (cxt^.len) a') (App (Wk t) coev0 i Source)
            Just body ->
              pure $ Just $ Lam x i Source (quote (cxt^.len) a') body

    (VU _, VU _) | StageExp h n <- vStage s, StageExp h' n' <- vStage s' -> do
      case () of
        _ | h == h', n < n' ->
              pure $ Just $! nTimes (n' - n) Code t
          | SHZero <- h, SHVar x <- h', n < n' -> do
              solveStage x SZero
              pure $ Just $! nTimes (n' - n) Code t
          | otherwise ->
              justUnify cxt a s a' s'

    (a@(VNe (HMeta _) _), a'                  ) -> goFlex cxt t a s a' s'
    (a,                   a'@(VNe (HMeta _) _)) -> goFlex cxt t a s a' s'

    (VCode a, a') -> Just <$> coerce cxt (Down t) a (vPred s) a' s'
    (a, VCode a') -> Just . Up <$> coerce cxt t a s a' (vPred s')
    (a, a')       -> justUnify cxt a s a' s'



checkU :: Dbg => Cxt -> Raw -> StageExp -> IO Tm
checkU cxt t s = check cxt t (VU s) s

check :: Dbg => Cxt -> Raw -> VTy -> StageExp -> IO Tm
check cxt topT ~topA topS = case (topT, force topA) of
  (RSrcPos p t, a) ->
    addSrcPos p (check cxt t a topS)

  (RLam x ann i t, VPi x' i' a b) | i == i' -> do
    ann <- case ann of
      Just ann -> do
        ann <- checkU cxt ann topS
        unifyWhile cxt (eval (cxt^.vals) ann) a topS
        pure ann
      Nothing ->
        pure $ quote (cxt^.len) a
    t <- check (bind x Source a topS cxt) t (b (VVar (cxt^.len))) topS
    pure $ Lam x i Source ann t

  (t, VPi x Impl a b) -> do
    t <- check (bind x Inserted a topS cxt) t (b (VVar (cxt^.len))) topS
    pure $ Lam x Impl Inserted (quote (cxt^.len) a) t

  (RCode a, VU (SSuc s)) -> do
    Code <$> checkU cxt a s

  (RPi x i a b, VU s) -> do
    a <- checkU cxt a s
    let ~va = eval (cxt^.vals) a
    b <- checkU (bind x Source va s cxt) b s
    pure $ Pi x i a b

  (RUp t, VCode a) -> do
    Up <$> check cxt t a (vPred topS)

  (t, VCode a) -> do
    Up <$> check cxt t a (vPred topS)

  (RLet x a t u, topA) -> do
    (a, s) <- inferU cxt a
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va s
    let ~vt = eval (cxt^.vals) t
    u <- check (define x va s vt cxt) u topA topS
    pure $ Let x a s t u

  (RHole, topA) -> do
    freshMeta cxt topA topS

  (t, topA) -> do
    (t, va, s) <- insert cxt $ infer cxt t
    coerce cxt t va s topA topS


-- | We specialcase top-level lambdas (serving as postulates) for better
--   printing: we don't print them in meta spines. We prefix the top
--   lambda-bound names with '*'.
inferTop :: Dbg => Cxt -> Raw -> IO (Tm, VTy, StageExp)
inferTop cxt = \case
  RLam x ann i t -> do
    (a, s) <- case ann of
      Just ann -> inferU cxt ann
      Nothing  -> do
        s <- freshStage
        m <- freshMeta cxt (VU s) s
        pure (m, s)
    let ~va = eval (cxt^.vals) a
    (t, liftVal cxt -> !b, s') <- inferTop (bind ('*':x) Source va s cxt) t
    unifyStage s s'
    pure (Lam x i Source a t, VPi x i va b, s')
  RSrcPos p t ->
    addSrcPos p $ inferTop cxt t
  RLet x a t u -> do
    (a, s) <- inferU cxt a
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va s
    let ~vt = eval (cxt^.vals) t
    (u, b, s') <- inferTop (define x va s vt cxt) u
    pure (Let x a s t u, b, s')
  t -> infer cxt t

infer :: Dbg => Cxt -> Raw -> IO (Tm, VTy, StageExp)
infer cxt = \case
  RSrcPos p t -> addSrcPos p $ infer cxt t

  RU s -> do
    s <- maybe freshStage (pure . sLit) s
    pure (U s, VU s, s)

  RVar x -> do
    let go :: [Name] -> [Origin] -> Types -> Int -> IO (Tm, VTy, StageExp)
        go (y:xs) (Source:os) (TSnoc _  a s) i | x == y || ('*':x) == y = pure (Var i, a, s)
        go (_:xs) (_       :os) (TSnoc as _ _) i = go xs os as (i + 1)
        go []     []            TNil           _ = report cxt (NameNotInScope x)
        go _ _ _ _ = error "impossible"
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  RPi x i a b -> do
    (a, s) <- inferU cxt a
    let ~va = eval (cxt^.vals) a
    b <- checkU (bind x Source va s cxt) b s
    pure (Pi x i a b, VU s, s)

  RApp t u i -> do
    (t, va, s) <- case i of Expl -> insert' cxt $ infer cxt t
                            _    -> infer cxt t
    case force va of
      VPi x i' a b -> do
        unless (i == i') $
          report cxt $ IcitMismatch i i'
        u <- check cxt u a s
        pure (App t u i Source, b (eval (cxt^.vals) u), s)

      -- a bit shitty!
      va -> do
        (u, dom, s') <- infer cxt u
        cod <- freshMeta (bind "x" Inserted dom s' cxt) (VU s') s'
        let vcod ~x = eval (VDef (cxt^.vals) x) cod
        -- traceShowM ("apparg", showTm (cxt^.names) u, showVal cxt dom, s')
        -- traceShowM ("appfun", showTm (cxt^.names) t, showVal cxt va, s)
        t <- coerce cxt t va s (VPi "x" i dom vcod) s'
        pure (App t u i Source, vcod (eval (cxt^.vals) u), s')

      -- VNe (HMeta m) sp -> do
      --   a    <- eval (cxt^.vals) <$> freshMeta cxt (VU s) s
      --   cod  <- freshMeta (bind "x" NOInserted a s cxt) (VU s) s
      --   let b ~x = eval (VDef (cxt^.vals) x) cod
      --   unifyWhile cxt (VNe (HMeta m) sp) (VPi "x" i a b) s
      --   u <- check cxt u a s
      --   pure (App t u i, b (eval (cxt^.vals) u), s)
      -- _ ->
      --   report (cxt^.names) $ ExpectedFunction (quote (cxt^.len) va)

  RLam x ann i t -> do
    (a, s) <- case ann of
      Just ann -> inferU cxt ann
      Nothing  -> do
        s <- freshStage
        m <- freshMeta cxt (VU s) s
        pure (m, s)
    let ~va = eval (cxt^.vals) a
    let cxt' = bind x Source va s cxt
    (t, liftVal cxt -> !b, s') <- insert cxt' $ infer cxt' t
    unifyStage s s'
    pure (Lam x i Source a t, VPi x i va b, s)

  RHole -> do
    s <- freshStage
    a <- freshMeta cxt (VU s) s
    let ~va = eval (cxt^.vals) a
    t <- freshMeta cxt va s
    pure (t, va, s)

  RLet x a t u -> do
    (a, s) <- inferU cxt a
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va s
    let ~vt = eval (cxt^.vals) t
    (u, b, s') <- infer (define x va s vt cxt) u
    pure (Let x a s t u, b, s')

  RCode a -> do
    (a, SSuc -> !s) <- inferU cxt a
    pure (Code a, VU s, s)

  RUp t -> do
    (t, a, s) <- infer cxt t
    pure (Up t, VCode a, SSuc s)

  RDown t -> do
    s <- freshStage
    a <- eval (cxt^.vals) <$> freshMeta cxt (VU s) s
    (t, a', s') <- infer cxt t
    unifyStage s' (SSuc s)
    unifyWhile cxt a' (VCode a) s'
    pure (Down t, a, s)
