
{-|
Evaluation for the purpose of post-processing elaborated terms. Performs:

1. unfolding meta solutions (zonking)
2. computing away curried functions
3. staging

-}

module PostEval where

import Types (Name, Lvl, MId, Spine, StageExp(..), StageId, Icit, Stage, Tm(..), Ix)
import Evaluation (vStage)

type VTy = Val

data Val
  = VVar Lvl
  | VLet Name VTy Stage Val Val
  | VU Stage
  | VUnfoldMeta Val

  | VPi Name Icit VTy (Val -> Val)
  | VLam Name Icit VTy (Val -> Val)
  | VApp Val Val Icit

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

stage :: Stage -> Stage -> a -> a -> a
stage s s' x y = if s <= s' then x else y

vVar :: Vals -> Stage -> Stage -> Ix -> Val
vVar vs s s' x = go vs x where
  go :: Vals -> Ix -> Val
  go (VDef vs v) 0 = stage s s' v (VVar (valsLen vs))
  go (VSkip vs)  0 = VVar (valsLen vs)
  go (VDef vs _) x = go vs (x - 1)
  go (VSkip vs)  x = go vs (x - 1)
  go _           _ = error "impossible"

sPred :: Stage -> Stage
sPred s = if s > 0 then s - 1 else error "impossible"

eval :: Vals -> Stage -> Stage -> Tm -> Val
eval vs s s' = go where
  go :: Tm -> Val
  go = \case
    Var x ->
      vVar vs s s' x
    App t u i -> case (go t, go u) of
     (f@(VLam x i a t), !u) -> stage s s' (t u) (VApp f u i)
     (t, u)                 -> VApp t u i
    Let x a s'' t u -> case vStage s'' of
      SLit s'' ->
        let ~t' = eval vs s s'' t in
        stage s s''
          (eval (VDef vs t') s s' u)
          (VLet x (eval vs s s'' a) s'' t' (eval (VSkip vs) s s' u))
      _ -> error "impossible"

    Pi x i a b  -> VPi x i (go a) (goBind b)
    Lam x i a t -> VLam x i (go a) (goBind t)
    Code a      -> VCode (eval vs s (sPred s') a)
    Up t        -> VUp (eval vs s (sPred s') t)
    Down t      -> VDown (eval vs s (succ s') t)
    Tel _       -> VTel s'
    TEmpty      -> VTEmpty
    TCons x a b -> VTCons x (go a) (goBind b)
    Rec a       -> VRec (go a)
    Tempty      -> VTempty
    Tcons t u   -> VTcons (go t) (go u)
    Proj1 t     -> case go t of VTcons t u -> t; t -> VProj1 t
    Proj2 t     -> case go t of VTcons t u -> u; t -> VProj2 t

    -- PiTel x a b -> case go a of VTCons  y a b -> _
    --                             VTEmpty       -> goBind b



  goBind :: Tm -> Val -> Val
  goBind t ~v = eval (VDef vs v) s s' t
