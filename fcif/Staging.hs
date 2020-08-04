{-|
Evaluation for the purpose of post-processing elaborated terms. Performs:

1. Computing away curried functions.
2. Staging. A redex is computed iff it is at or above the stage given
   as parameter. For example, staging at level 0 is just normalization.
   Staging at level 1 is traditional staged compilation.

Assumes that input is zonked.
-}

module Staging (stage)  where

import Types (Name, Lvl, MId, Icit(..), Stage, Tm(..), Ix, sLit, Origin(..))
import Evaluation (sExp2Lit)

type VTy = Val

data Val
  = VVar Lvl
  | VLet Name VTy Stage Val (Val -> Val)
  | VU Stage
  | VMeta MId

  | VPi Name Icit VTy (Val -> Val)
  | VLam Name Icit Origin VTy (Val -> Val)
  | VApp Val Val Icit Origin

  | VCode Val
  | VUp Val
  | VDown Val

  | VTel Stage
  | VTEmpty
  | VTCons Name VTy (Val -> VTy)
  | VRec VTy
  | VTempty
  | VTcons Val Val
  | VProj1 Val
  | VProj2 Val
  | VPiTel Name VTy (Val -> VTy)
  | VAppTel VTy Val Val
  | VLamTel Name VTy (Val -> Val)

data Vals = VNil | VDef Vals ~Val | VSkip Vals

valsLen :: Vals -> Int
valsLen = go 0 where
  go acc VNil        = acc
  go acc (VDef vs _) = go (acc + 1) vs
  go acc (VSkip vs)  = go (acc + 1) vs

cmpStage :: Stage -> Stage -> a -> a -> a
cmpStage s s' x y = if s <= s' then x else y

vVar :: Vals -> Stage -> Stage -> Ix -> Val
vVar vs s s' x = go vs x where
  go :: Vals -> Ix -> Val
  go (VDef vs v) 0 = v
  go (VSkip vs)  0 = VVar (valsLen vs)
  go (VDef vs _) x = go vs (x - 1)
  go (VSkip vs)  x = go vs (x - 1)
  go _           _ = error "impossible"

sPred :: Stage -> Stage
sPred s = if s > 0 then s - 1 else error "impossible"

vApp :: Val -> Val -> Icit -> Origin -> Val
vApp t u i o = case (t, u) of
  (f@(VLam x i _ a t), !u) -> t u
  (t, u)                   -> VApp t u i o

vProj1 :: Val -> Val
vProj1 (VTcons t u) = t
vProj1 t            = VProj1 t

vProj2 :: Val -> Val
vProj2 (VTcons t u) = u
vProj2 t            = VProj2 t

vPiTel :: Name -> VTy -> (Val -> Val) -> Val
vPiTel x a b = case a of
  VTEmpty        -> b VTempty
  VTCons x1 a as -> let x1 = x ++ "1"
                        x2 = x ++ "2"
                    in VPi x1 Impl a $ \ ~x1 ->
                       vPiTel x2 (as x1) $ \ ~x2 -> b (VTcons x1 x2)
  a              -> VPiTel x a b

vLamTel :: Name -> VTy -> (Val -> Val) -> Val
vLamTel x a t = case a of
  VTEmpty       -> t VTempty
  VTCons _ a as -> let x1 = x ++ "1"
                       x2 = x ++ "2"
                   in VLam x1 Impl Inserted a $ \ ~x1 ->
                      vLamTel x2 (as x1) $ \ ~x2 -> t (VTcons x1 x2)
  a             -> VLamTel x a t

vAppTel :: VTy -> Val -> Val -> Val
vAppTel a ~t ~u = case a of
  VTEmpty       -> t
  VTCons _ a as -> let u1 = vProj1 u in vAppTel (as u1) (vApp t u1 Impl Inserted) (vProj2 u)
  a             -> case t of
                     VLamTel _ _ t -> t u
                     t             -> VAppTel a t u

vUp :: Val -> Val
vUp = \case
  VDown t -> t
  t       -> VUp t

vDown :: Val -> Val
vDown = \case
  VUp t -> t
  t     -> VDown t

valsTail :: Vals -> Vals
valsTail = \case
  VDef vs _ -> vs
  VSkip vs  -> vs
  _         -> error "impossible"

eval :: Vals -> Stage -> Stage -> Tm -> Val
eval vs s s' = go where
  go :: Tm -> Val
  go = \case
    Var x ->
      vVar vs s s' x
    Let x a (sExp2Lit -> s'') t u ->
      let ~t' = eval vs s s'' t in
      cmpStage s s''
        (eval (VDef vs t') s s' u)
        (VLet x (eval vs s s'' a) s'' t' (goBind u))

    Pi x i a b    -> VPi x i (go a) (goBind b)
    Lam x i o a t -> VLam x i o (go a) (goBind t)
    App t u i o   -> cmpStage s s' (vApp (go t) (go u) i o) (VApp (go t) (go u) i o)

    U s          -> VU (sExp2Lit s)
    Meta m       -> VMeta m
    Skip t       -> eval (VSkip vs) s s' t
    Wk t         -> eval (valsTail vs) s s' t

    Code a       -> VCode (eval vs s (sPred s') a)
    Up t         -> let t' = eval vs s (sPred s') t in
                    vUp t'
    Down t       -> let t' = eval vs s (succ s') t in
                    vDown t'
    Tel _        -> VTel s'
    TEmpty       -> VTEmpty
    TCons x a b  -> VTCons x (go a) (goBind b)
    Rec a        -> VRec (go a)
    Tempty       -> VTempty
    Tcons t u    -> VTcons (go t) (go u)
    Proj1 t      -> case go t of VTcons t u -> t; t -> VProj1 t
    Proj2 t      -> case go t of VTcons t u -> u; t -> VProj2 t
    PiTel x a b  -> vPiTel x (go a) (goBind b)
    LamTel x a t -> vLamTel x (go a) (goBind t)
    AppTel a t u -> vAppTel (go a) (go t) (go u)

  goBind :: Tm -> Val -> Val
  goBind t ~v = eval (VDef vs v) s s' t

quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case v of
    VVar x         -> Var (d - x - 1)
    VMeta m        -> Meta m
    VLet x a s t u -> Let x (go a) (sLit s) (go t) (goBind u)
    VApp t u i o   -> App (go t) (go u) i o
    VCode a        -> Code (go a)
    VUp t          -> Up (go t)
    VDown t        -> Down (go t)
    VProj1 t       -> Proj1 (go t)
    VProj2 t       -> Proj2 (go t)
    VAppTel a t u  -> AppTel (go a) (go t) (go u)
    VLam x i o a t -> Lam x i o (go a) (goBind t)
    VPi x i a b    -> Pi x i (go a) (goBind b)
    VU s           -> U (sLit s)
    VTel s         -> Tel (sLit s)
    VRec a         -> Rec (go a)
    VTEmpty        -> TEmpty
    VTCons x a as  -> TCons x (go a) (goBind as)
    VTempty        -> Tempty
    VTcons t u     -> Tcons (go t) (go u)
    VPiTel x a b   -> PiTel x (go a) (goBind b)
    VLamTel x a t  -> LamTel x (go a) (goBind t)

  goBind t = quote (d + 1) (t (VVar d))

stage :: Stage -> Stage -> Tm -> Tm
stage s s' = quote 0 . eval VNil s s'
