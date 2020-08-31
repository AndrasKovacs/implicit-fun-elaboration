{-# options_ghc -Wno-orphans #-}

module Pretty (showTm, showTopTm, dbgTm, dbgVal) where

import Prelude hiding (pi)
import Lens.Micro.Platform

import Types
import Evaluation

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p < p')

-- Precedences
atomp = 3  -- identifiers, U, ε, Tel
appp  = 2  -- application (functions, π₁, π₂, Rec): assocs to left
recp  = 1  -- _∷_ : assocs to right
tmp   = 0  -- lam, let, Pi, PiTel, _▷_ : assocs to right

fresh :: [Name] -> Name -> Name
fresh _ "_" = "_"
fresh ns n | elem n ns = fresh ns (n++"'")
           | otherwise = n

bracket :: ShowS -> ShowS
bracket s = ('{':).s.('}':)

-- | Prints a spine, also returns whether the spine is meta-headed.
spine :: [Name] -> Tm -> (ShowS, Bool)
spine ns (App (spine ns -> (tp, metasp)) u i) =
  -- we don't print top-level lambda-bound args in meta spines
  let up | True <- metasp, Var x <- u, '*':_ <- ns !! x =
             id
         | otherwise =
             (' ':) . icit i (bracket (tm tmp ns u)) (tm atomp ns u)
  in (tp . up, metasp)
spine ns (Meta m) =
  (tm atomp ns (Meta m), True)
spine ns t =
  (tm atomp ns t, False)

lamBind :: Name -> Icit -> ShowS
lamBind x i = icit i bracket id ((if null x then "_" else x) ++)

lams :: [Name] -> Tm -> ShowS
lams ns (Lam (fresh ns -> x) i a t) =
  (' ':) . lamBind x i . lams (x:ns) t
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
tm p ns = \case
  Var x  -> case ns !! x of
    '*':n -> (n++)
    "_"   -> ("@"++).(show x++)
    n     -> (n++)
  Meta m ->
    ("?"++).(show m++)
  Let (fresh ns -> x) a t u ->
    par tmp p $
      ("let "++).(x++).(" : "++). tm tmp ns a . ("\n    = "++)
      . tm tmp ns t . ("\nin\n"++) . tm tmp (x:ns) u
  t@App{} ->
    par appp p $ fst $ spine ns t
  Lam x i a t ->
    par tmp p $ ("λ "++) . lamBind x i . lams (x:ns) t

  Pi "_" Expl a b ->
    par tmp p $ tm recp ns a . (" → "++) . tm tmp ("_":ns) b
  Pi (fresh ns -> x) i a b ->
    par tmp p $ piBind ns x i a . pi (x:ns) b

  Check m t -> tm p ns t
  U         -> ("U"++)
  Skip t    -> tm p ("_":ns) t

-- | We specialcase printing of top lambdas, since they are usually used
--   to postulate stuff. We use '*' in a somewhat hacky way to mark
--   names bound in top lambdas, so that later we can avoid printing
--   them in meta spines.
top :: String -> String -> [Name] -> Tm -> ShowS
top pre post ns (Lam (fresh ns -> x) i a t) =
    (pre++)
  . icit i bracket (showParen True) (
         ((if null x then "_" else x)++) . (" : "++) . tm tmp ns a)
  . top "\n " ".\n\n" (('*':x):ns) t -- note the '*'
top pre post ns (Let (fresh ns -> x) a t u) =
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
