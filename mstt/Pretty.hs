{-# options_ghc -Wno-orphans #-}

module Pretty (showTm, showTopTm, dbgVal, dbgTm) where

import Lens.Micro.Platform
import Prelude hiding (pi)
import Types
import Evaluation
import ElabState

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

-- Precedences
atomp = 3  -- identifiers, U, ε, Tel
appp  = 2  -- application (functions, π₁, π₂, Rec): assocs to left
recp  = 1  -- _∷_ : assocs to right
tmp   = 0  -- lam, let, Pi, _▷_ : assocs to right

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns || elem ('*':x) ns = go (1 :: Int) where
  go n | elem (x ++ show n) ns || elem ('*':x ++ show n) ns = go (n + 1)
       | otherwise = x ++ show n
fresh ns x = x

bracket :: ShowS -> ShowS
bracket s = ('{':).s.('}':)

stage :: StageExp -> ShowS
stage s = case vStage s of
  StageExp (SHVar x) 0 -> ('?':).(show x++)
  StageExp (SHVar x) n -> showParen True (('?':).(show x++).(" + "++).(show n++))
  StageExp SHZero    n -> (show n++)

instance Show StageExp where
  show s = stage s []

-- | Prints a spine, also returns whether a) the spine is meta-headed,
--   b) the spine is an atom when implicit applications are omitted.
spine :: [Name] -> Tm -> (ShowS, Bool, Bool)
spine ns (App (spine ns -> (tp, metasp, isAtom)) u i o) =
  showingInsertions $ \case
    b | (o == Source) || b ->
        let up | True <- metasp, Var x <- u, '*':_ <- ns !! x =
                   id
               | otherwise =
                   (' ':) . icit i (bracket (tm tmp ns u)) (tm atomp ns u)
        in (tp . up, metasp, False)
      | otherwise ->
        (tp, metasp, isAtom)
spine ns (Meta m) =
  (tm atomp ns (Meta m), True, True)
spine ns t =
  (tm atomp ns t, False, True)

lamBind :: Name -> Icit -> ShowS
lamBind x i = icit i bracket id ((if null x then "_" else x) ++)

lams :: [Name] -> Tm -> ShowS
lams ns (Lam (fresh ns -> x) i o a t) =
  showingInsertions $ \case
    b | (o == Source) || b ->
        (' ':) . lamBind x i . lams (x:ns) t
      | otherwise ->
        lams (x:ns) t
lams ns t =
  (". "++) . tm tmp ns t

piBind :: [Name] -> Name -> Icit -> Tm -> ShowS
piBind ns x i a =
  icit i bracket (showParen True) ((x++) . (" : "++) . tm tmp ns a)

pi :: [Name] -> Tm -> ShowS
pi ns (Pi (fresh ns -> x) i a b)  | x /= "_" =
  piBind ns x i a . pi (x:ns) b
pi ns t = (" → "++) . tm tmp ns t

tm :: Int -> [Name] -> Tm -> ShowS
tm p ns = go p where

  go :: Int -> Ty -> [Char] -> [Char]
  go p = \case
    Var x  -> case ns !! x of
      '*':n -> (n++)
      "_"   -> ("@"++).(show x++)
      n     -> (n++)
    Meta m ->
      ("?"++).(show m++)
    Let (fresh ns -> x) a _ t u ->
      par p tmp $
        ("let "++).(x++).(" : "++). go tmp a . (" = "++)
        . go tmp t . (" in "++) . tm tmp (x:ns) u
    t@App{} ->
      let (t', _, isAtom) = spine ns t
      in par p (if isAtom then atomp else appp) t'

    Lam (fresh ns -> x) i Inserted a t ->
      showingInsertions $ \case
        True  -> par p tmp $ ("λ "++) . lamBind x i . lams (x:ns) t
        False -> case t of Lam{} -> par p tmp $ ("λ"++) . lams (x:ns) t
                           _     -> go p t
    Lam (fresh ns -> x) i _ a t ->
      par p tmp $ ("λ "++) . lamBind x i . lams (x:ns) t

    Pi "_" Expl a b ->
      par p tmp $ go recp a . (" → "++) . tm tmp ("_":ns) b
    Pi (fresh ns -> x) i a b ->
      par p tmp $ piBind ns x i a . pi (x:ns) b

    U s    -> par p appp (("U "++) . stage s)
    Tel s  -> par p appp (("Tel "++) . stage s)
    TEmpty -> ("ε"++)

    TCons "_" a as ->
      par p tmp $ go recp a . (" ▷ "++). go tmp as
    TCons (fresh ns -> x) a as ->
      par p tmp $
        showParen True ((x++) . (" : "++) . go tmp a)
        . (" ▷ "++). tm tmp (x:ns) as

    Tempty    -> ("[]"++)
    Rec a     -> par p appp $ ("Rec "++) . go atomp a
    Tcons t u -> par p recp (go appp t . (" ∷ "++). go recp u)
    Proj1 t   -> par p appp (("π₁ "++). go atomp t)
    Proj2 t   -> par p appp (("π₂ "++). go atomp t)

    Skip t -> par p appp (("_skip_ "++).tm p ("_":ns) t)
    Wk t   -> par p appp (("_wk_ "++).tm p (tail ns) t)

    Code a -> par p appp $ ("^"++) . go atomp a
    Up t   -> ('<':).go tmp t.('>':)
    Down t -> ('[':).go tmp t.(']':)

-- | We specialcase printing of top lambdas, since they are usually used
--   to postulate stuff. We use '*' in a somewhat hacky way to mark
--   names bound in top lambdas, so that later we can avoid printing
--   them in meta spines.
top :: String -> String -> [Name] -> Tm -> ShowS
top pre post ns (Lam (fresh ns -> x) i o a t) =
    (pre++)
  . icit i bracket (showParen True) (
         ((if null x then "_" else x)++) . (" : "++) . tm tmp ns a)
  . top "\n " ".\n\n" (('*':x):ns) t -- note the '*'
top pre post ns (Let (fresh ns -> x) a s t u) =
    (post++)
  . ("let "++).(x++).(" : "++). tm tmp ns a . ("\n    = "++)
  . tm tmp ns t . ("\nin\n"++) . top "\nλ" "" (x:ns) u
top pre post ns t = (post++) . tm tmp ns t

showTm :: Cxt -> Tm -> String
showTm cxt t = tm tmp (cxt^.names) t []

showTopTm :: Tm -> String
showTopTm t = top "λ" "" [] t []

deriving instance Show Tm

dbgVal :: Cxt -> Val -> String
dbgVal cxt v = showTm cxt (quote (cxt^.len) v)

dbgTm :: Cxt -> Tm -> String
dbgTm = showTm
