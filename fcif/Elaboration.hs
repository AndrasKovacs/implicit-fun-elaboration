

module Elaboration where

import Control.Exception
import Control.Monad
import Data.Maybe
import Lens.Micro.Platform
import Data.IORef
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS


import Types
import Evaluation
import ElabState
import Errors

-- import Debug.Trace


-- Context operations
--------------------------------------------------------------------------------

emptyCxt :: Cxt
emptyCxt = Cxt VNil TNil [] [] 0

-- | Add a bound variable.
bind :: Name -> NameOrigin -> VTy -> Cxt -> Cxt
bind x o ~a (Cxt vs tys ns no d) =
  Cxt (VSkip vs) (TBound tys a) (x:ns) (o:no) (d + 1)

-- | Add a bound variable which comes from surface syntax.
bindSrc :: Name -> VTy -> Cxt -> Cxt
bindSrc x = bind x NOSource

-- | Define a new variable.
define :: Name -> VTy -> Val -> Cxt -> Cxt
define x ~a ~t (Cxt vs tys ns no d) =
  Cxt (VDef vs t) (TDef tys a) (x:ns) (NOSource:no) (d + 1)

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
    SNil        -> pure (mempty, 0, [])
    SApp sp u i -> do
      (!r, !d, !xs) <- go sp
      case force u of
        VVar x | IM.member x r -> throwIO $ NonLinearSpine x
               | otherwise     -> pure (IM.insert x d r, d + 1, x:xs)
        _      -> throwIO SpineNonVar

-- | Close a type in a cxt by wrapping it in Pi types and explicit strengthenings.
closingTy :: Cxt -> Ty -> Ty
closingTy cxt = go (cxt^.types) (cxt^.names) (cxt^.len) where
  go TNil                  []     d b = b
  go (TDef tys a)          (x:ns) d b = go tys ns (d-1) (Skip b)
  go (TBound tys a)        (x:ns) d b = go tys ns (d-1) (Pi x Expl (quote (d-1) a) b)
  go _                     _      _ _ = error "impossible"

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`, and the binder names from a list. If we run out of provided
--   binder names, we pick the names from the Pi domains.
closingTm :: (VTy, Int, [Name]) -> Tm -> Tm
closingTm = go 0 where
  getName []     x = x
  getName (x:xs) _ = x

  go d (a, 0, _)   rhs = rhs
  go d (a, len, xs) rhs = case force a of
    VPi (getName xs -> x) i a b  ->
      Lam x i (quote d a)  $ go (d + 1) (b (VVar d), len-1, drop 1 xs) rhs
    _            -> error "impossible"

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
          go acc (SApp sp (VVar x) i)    = go (isJust (IM.lookup x (str^.ren)) : acc) sp
          go _   _                       = Nothing

    case pruning of
      Nothing                    -> pure ()  -- spine is not a var substitution
      Just pruning | and pruning -> pure ()  -- no pruneable vars
      Just pruning               -> do

        metaTy <- lookupMeta m >>= \case
          Unsolved _ a -> pure a
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

        m' <- newMeta $ Unsolved mempty (eval VNil prunedTy)

        let argNum = length pruning
            body = go pruning metaTy (Meta m') 0 where
              go [] a acc d = acc
              go (True:pr) (force -> VPi x i a b) acc d =
                go pr (b (VVar d)) (App acc (Var (argNum - d - 1)) i) (d + 1)
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
    VLam x i a t     -> Lam x i <$> go a <*> goBind t
    VU               -> pure U

  goBind t = strengthen (liftStr str) (t (VVar (str^.cod)))

  goSp h = \case
    SNil           -> pure h
    SApp sp u i    -> App <$> goSp h sp <*> go u <*> pure i

-- | Unify the result of a postponed checking with its representative
--   metavariable.
unifyUncheckedRes :: Dbg => Cxt -> Tm -> (MId, Spine) -> IO ()
unifyUncheckedRes cxt t (m, sp) =
  lookupMeta m >>= \case

    -- If the postponed term is unconstrained and doesn't block anything,
    -- solving its meta cannot fail, so we solve it lazily. If nothing depends
    -- on this solution, it's never computed.
    Unsolved bs a | IS.null bs -> do
      let ~solution =
            -- traceShow ("force postponed", m) $
            runIO (getSolution cxt bs a m sp (eval (cxt^.vals) t))
      writeMeta m (Solved solution)
      -- traceShowM ("postponed thunk", m)

    Unsolved _ _ ->
      unify cxt (eval (cxt^.vals) t) (force (VNe (HMeta m) sp))
    Solved{} ->
      unify cxt (eval (cxt^.vals) t) (force (VNe (HMeta m) sp))
    _ ->
      error "impossible"

retryCheck :: Dbg => MId -> IO ()
retryCheck m = lookupMeta m >>= \case
  Unchecked cxt t a res@(_, _) -> do
    -- traceShowM ("resume", m, t)
    case force a of
      VNe (HMeta m') sp ->
        addBlocking m m'
      a -> do
        t <- check cxt t a
        unifyUncheckedRes cxt t res
        -- traceShowM ("checked", m)
        writeMeta m $ Checked t

  Checked{} -> pure ()
  _         -> error "impossible"

checkAll :: MId -> IO ()
checkAll m = do
  m' <- readIORef nextMId
  when (m < m') $ do
    lookupMeta m >>= \case
      Unchecked cxt t topA res -> do
        (t, va) <- insert cxt $ infer cxt t
        writeMeta m (Checked t)
        unifyWhile cxt va topA
        unifyUncheckedRes cxt t res
      _ -> pure ()
    checkAll (m + 1)

getSolution :: Cxt -> Blocking -> VTy -> MId -> Spine -> Val -> IO Val
getSolution cxt blocked metaTy m sp rhs = do
  -- these normal forms are only used in error reporting
  let ~topLhs = quote (cxt^.len) (VNe (HMeta m) sp)
      ~topRhs = quote (cxt^.len) rhs

  -- check spine
  (ren, spLen, spVars) <- checkSp sp
         `catch` (throwIO . SpineError cxt topLhs topRhs)

  --  strengthen right hand side
  rhs <- strengthen (Str spLen (cxt^.len) ren (Just m)) rhs
         `catch` (throwIO . StrengtheningError cxt topLhs topRhs)

  let spVarNames = map (lvlName cxt) spVars
  let closedRhs  = closingTm (metaTy, spLen, spVarNames) rhs
  let ~res = eval VNil closedRhs
  pure res

-- | May throw `UnifyError`.
solveMeta :: Dbg => Cxt -> MId -> Spine -> Val -> IO ()
solveMeta cxt m sp rhs = do
  (blocked, metaTy) <- lookupMeta m >>= \case
    Unsolved blocked a -> pure (blocked, a)
    _                  -> error "impossible"
  solution <- getSolution cxt blocked metaTy m sp rhs
  writeMeta m (Solved solution)

  forM_ (IS.toList blocked) retryCheck

-- | Create a fresh meta with given type, return
--   the meta applied to all bound variables.
freshMeta :: Cxt -> VTy -> IO Tm
freshMeta cxt (quote (cxt^.len) -> a) = do
  let metaTy = closingTy cxt a
  m <- newMeta $ Unsolved mempty (eval VNil metaTy)

  let vars :: Types -> (Spine, Lvl)
      vars TNil                                 = (SNil, 0)
      vars (TDef (vars -> (sp, !d)) _)          = (sp, d + 1)
      vars (TBound (vars -> (sp, !d)) _)        = (SApp sp (VVar d) Expl, d + 1)

  let sp = fst $ vars (cxt^.types)
  pure (quote (cxt^.len) (VNe (HMeta m) sp))

-- | Wrap the inner `UnifyError` arising from unification in an `UnifyErrorWhile`.
--   This decorates an error with one additional piece of context.
unifyWhile :: Dbg => Cxt -> Val -> Val -> IO ()
unifyWhile cxt l r =
  unify cxt l r
  `catch`
  (report cxt . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))

-- | May throw `UnifyError`.
unify :: Dbg => Cxt -> Val -> Val -> IO ()
unify cxt l r = go l r where

  unifyError =
    throwIO $ UnifyError cxt (quote (cxt^.len) l) (quote (cxt^.len) r)

  -- if both sides are meta-headed, we simply try to check both spines
  flexFlex m sp m' sp' = do
    try @SpineError (checkSp sp) >>= \case
      Left{}  -> solveMeta cxt m' sp' (VNe (HMeta m) sp)
      Right{} -> solveMeta cxt m sp (VNe (HMeta m') sp')

  go :: Dbg => Val -> Val -> IO ()
  go t t' = case (force t, force t') of
    (VLam x _ a t, VLam _ _ _ t')            -> goBind x a t t'
    (VLam x i a t, t')                       -> goBind x a t (\ ~v -> vApp t' v i)
    (t, VLam x' i' a' t')                    -> goBind x' a' (\ ~v -> vApp t v i') t'
    (VPi x i a b, VPi x' i' a' b') | i == i' -> go a a' >> goBind x a b b'
    (VU, VU)                                 -> pure ()
    (VNe h sp, VNe h' sp') | h == h'         -> goSp sp sp'
    (VNe (HMeta m) sp, VNe (HMeta m') sp')   -> flexFlex m sp m' sp'
    (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t'
    (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t
    _                                        -> unifyError

  goBind x a t t' =
    let v = VVar (cxt^.len) in unify (bindSrc x a cxt) (t v) (t' v)

  goSp sp sp' = case (sp, sp') of
    (SNil, SNil)                            -> pure ()
    (SApp sp u i, SApp sp' u' i') | i == i' -> goSp sp sp' >> go u u'
    _                                       -> error "impossible"


-- Elaboration
--------------------------------------------------------------------------------

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = do
  (t, va) <- act
  let go t va = case force va of
        VPi x Impl a b -> do
          m <- freshMeta cxt a
          let mv = eval (cxt^.vals) m
          go (App t m Impl) (b mv)
        va -> pure (t, va)
  go t va

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _ _), va) -> pure (t, va)
  (t                 , va) -> insert' cxt (pure (t, va))

check :: Cxt -> Raw -> VTy -> IO Tm
check cxt topT ~topA = case (topT, force topA) of
  (RSrcPos p t, a) ->
    addSrcPos p (check cxt t a)

  (RLam x ann i t, VPi x' i' a b) | i == i' -> do
    ann <- case ann of
      Just ann -> do
        ann <- check cxt ann VU
        unifyWhile cxt (eval (cxt^.vals) ann) a
        pure ann
      Nothing ->
        pure $ quote (cxt^.len) a
    t <- check (bind x NOSource a cxt) t (b (VVar (cxt^.len)))
    pure $ Lam x i ann t

  (t, VPi x Impl a b) -> do
    t <- check (bind x NOInserted a cxt) t (b (VVar (cxt^.len)))
    pure $ Lam x Impl (quote (cxt^.len) a) t

  (t, topA@(VNe (HMeta m) sp)) -> do
    -- traceShowM ("postpone", t)

    -- create fresh meta for checking result
    res <- freshMeta cxt topA
    let VNe (HMeta m') sp = eval (cxt^.vals) res

    -- create fresh checking problem
    chk <- newMeta $ Unchecked cxt t topA (m' , sp)
    -- add chk to blocked set
    addBlocking chk m

    pure $ Check chk res

  (RLet x a t u, topA) -> do
    a <- check cxt a VU
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va
    let ~vt = eval (cxt^.vals) t
    u <- check (define x va vt cxt) u topA
    pure $ Let x a t u

  (RHole, topA) -> do
    freshMeta cxt topA

  (t, topA) -> do
    (t, va) <- insert cxt $ infer cxt t
    unifyWhile cxt va topA
    pure t

-- | We specialcase top-level lambdas (serving as postulates) for better
--   printing: we don't print them in meta spines. We prefix the top
--   lambda-bound names with '*'.
inferTop :: Cxt -> Raw -> IO (Tm, VTy)
inferTop cxt = \case
  RLam x ann i t -> do
    a <- case ann of
      Just ann -> check cxt ann VU
      Nothing  -> freshMeta cxt VU
    let ~va = eval (cxt^.vals) a
    (t, liftVal cxt -> b) <- inferTop (bind ('*':x) NOSource va cxt) t
    pure (Lam x i a t, VPi x i va b)

  RSrcPos p t ->
    addSrcPos p $ inferTop cxt t

  RLet x a t u -> do
    a <- check cxt a VU
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va
    let ~vt = eval (cxt^.vals) t
    (u, b) <- inferTop (define x va vt cxt) u
    pure (Let x a t u, b)

  t ->
    insert cxt $ infer cxt t

infer :: Cxt -> Raw -> IO (Tm, VTy)
infer cxt = \case
  RSrcPos p t -> addSrcPos p $ infer cxt t

  RU -> pure (U, VU)

  RVar x -> do
    let go :: [Name] -> [NameOrigin] -> Types -> Int -> IO (Tm, VTy)
        go (y:xs) (NOSource:os) (TSnoc _  a) i | x == y || ('*':x) == y = pure (Var i, a)
        go (_:xs) (_       :os) (TSnoc as _) i = go xs os as (i + 1)
        go []     []            TNil         _ = report cxt (NameNotInScope x)
        go _ _ _ _ = error "impossible"
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  RPi x i a b -> do
    a <- check cxt a VU
    let ~va = eval (cxt^.vals) a
    b <- check (bind x NOSource va cxt) b VU
    pure (Pi x i a b, VU)

  RApp t u i -> do
    (t, va) <- case i of Expl -> insert' cxt $ infer cxt t
                         _    -> infer cxt t
    case force va of
      VPi x i' a b -> do
        unless (i == i') $
          report cxt $ IcitMismatch i i'
        u <- check cxt u a
        pure (App t u i, b (eval (cxt^.vals) u))
      VNe (HMeta m) sp -> do
        a    <- eval (cxt^.vals) <$> freshMeta cxt VU
        cod  <- freshMeta (bind "x" NOInserted a cxt) VU
        let b ~x = eval (VDef (cxt^.vals) x) cod
        unifyWhile cxt (VNe (HMeta m) sp) (VPi "x" i a b)
        u <- check cxt u a
        pure (App t u i, b (eval (cxt^.vals) u))
      _ ->
        report cxt $ ExpectedFunction (quote (cxt^.len) va)

  RLam x ann i t -> do
    a <- case ann of
      Just ann -> check cxt ann VU
      Nothing  -> freshMeta cxt VU
    let ~va = eval (cxt^.vals) a
    let cxt' = bind x NOSource va cxt
    (t, liftVal cxt -> b) <- insert cxt' $ infer cxt' t
    pure (Lam x i a t, VPi x i va b)

  RHole -> do
    a <- freshMeta cxt VU
    let ~va = eval (cxt^.vals) a
    t <- freshMeta cxt va
    pure (t, va)

  RLet x a t u -> do
    a <- check cxt a VU
    let ~va = eval (cxt^.vals) a
    t <- check cxt t va
    let ~vt = eval (cxt^.vals) t
    (u, b) <- infer (define x va vt cxt) u
    pure (Let x a t u, b)
