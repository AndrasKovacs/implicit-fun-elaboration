{-# options_ghc -Wno-orphans #-}

module Pretty (showTm, showTopTm) where

import Prelude hiding (pi)
import Types

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
spine ns (AppTel a (spine ns -> (tp, metasp)) u) =
  (tp . (' ':) . bracket (tm tmp ns u . (" : "++) . tm tmp ns a), metasp)
spine ns (Meta m) =
  (tm atomp ns (Meta m), True)
spine ns t =
  (tm atomp ns t, False)

lamBind :: Name -> Icit -> ShowS
lamBind x i = icit i bracket id ((if null x then "_" else x) ++)

lamTelBind :: [Name] -> Name -> Tm -> ShowS
lamTelBind ns x a = bracket ((x++).(" : "++).tm tmp ns a)

lams :: [Name] -> Tm -> ShowS
lams ns (Lam (fresh ns -> x) i a t) =
  (' ':) . lamBind x i . lams (x:ns) t
lams ns (LamTel (fresh ns -> x) a t) =
  (' ':) . lamTelBind ns x a . lams (x:ns) t
lams ns t =
  (". "++) . tm tmp ns t

piBind :: [Name] -> Name -> Icit -> Tm -> ShowS
piBind ns x i a =
  icit i bracket (showParen True) ((x++) . (" : "++) . tm tmp ns a)

pi :: [Name] -> Tm -> ShowS
pi ns (Pi (fresh ns -> x) i a b)  | x /= "_" =
  piBind ns x i a . pi (x:ns) b
pi ns (PiTel (fresh ns -> x) a b) | x /= "_" =
  piBind ns x Impl a . pi (x:ns) b
pi ns t = (" → "++) . tm tmp ns t

stage :: StageExp -> ShowS
stage = \case
  SVar x -> ('?':).(show x++)
  SSuc s -> showParen True (("Suc "++).stage s)
  SLit s -> (show s++)

instance Show StageExp where
  show s = stage s []

tm :: Int -> [Name] -> Tm -> ShowS
tm p ns = \case
  Var x  -> case ns !! x of
    '*':n -> (n++)
    "_"   -> ("@"++).(show x++)
    n     -> (n++)
  Meta m ->
    ("?"++).(show m++)
  Let (fresh ns -> x) a _ t u ->
    par tmp p $
      ("let "++).(x++).(" : "++). tm tmp ns a . ("\n    = "++)
      . tm tmp ns t . ("\nin\n"++) . tm tmp (x:ns) u
  t@App{} ->
    par appp p $ fst $ spine ns t
  t@AppTel{} ->
    par appp p $ fst $ spine ns t
  Lam x i a t ->
    par tmp p $ ("λ "++) . lamBind x i . lams (x:ns) t

  Pi "_" Expl a b ->
    par tmp p $ tm recp ns a . (" → "++) . tm tmp ("_":ns) b
  Pi (fresh ns -> x) i a b ->
    par tmp p $ piBind ns x i a . pi (x:ns) b

  U s    -> par appp p (("U "++) . stage s)
  Tel s  -> par appp p (("Tel "++) . stage s)
  TEmpty -> ("ε"++)

  TCons "_" a as ->
    par tmp p $ tm recp ns a . (" ▷ "++). tm tmp ns as
  TCons (fresh ns -> x) a as ->
    par tmp p $
      showParen True ((x++) . (" : "++) . tm tmp ns a)
      . (" ▷ "++). tm tmp (x:ns) as

  Tempty    -> ("[]"++)
  Rec a     -> par appp p $ ("Rec "++) . tm atomp ns a
  Tcons t u -> par recp p (tm appp ns t . (" ∷ "++). tm recp ns u)
  Proj1 t   -> par appp p (("π₁ "++). tm atomp ns t)
  Proj2 t   -> par appp p (("π₂ "++). tm atomp ns t)

  PiTel "_" a b ->
    par tmp p $ tm recp ns a . (" → "++) . tm tmp ("_":ns) b
  PiTel (fresh ns -> x) a b ->
    par tmp p $ piBind ns x Impl a . pi (x:ns) b
  LamTel (fresh ns -> x) a t ->
    par tmp p $ ("λ"++) . lamTelBind ns x a . lams (x:ns) t

  Skip t -> tm p ("_":ns) t

  Code a -> par appp p $ ("^"++) . tm atomp ns a
  Up t   -> ('<':).tm tmp ns t.('>':)
  Down t -> par appp p $ ("~"++) . tm atomp ns t

-- | We specialcase printing of top lambdas, since they are usually used
--   to postulate stuff. We use '*' in a somewhat hacky way to mark
--   names bound in top lambdas, so that later we can avoid printing
--   them in meta spines.
showTopTm :: Tm -> String
showTopTm t = topLams False "λ" "" [] t [] where
  topLams :: Bool -> String -> String -> [Name] -> Tm -> ShowS
  topLams p pre post ns (Lam (fresh ns -> x) i a t) =
    showParen p (
      (pre++)
    . icit i bracket (showParen True) (
           ((if null x then "_" else x)++) . (" : "++) . tm tmp ns a)
    . topLams False "\n " ".\n\n" (('*':x):ns) t) -- note the '*'
  topLams _ pre post ns t = (post++) . tm tmp ns t


showTm ns t = tm tmp ns t []
instance Show Tm where show = showTopTm
-- showTm ns t = show t
-- deriving instance Show Tm
