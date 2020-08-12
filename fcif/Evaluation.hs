
module Evaluation where

import Types
import ElabState

import GHC.Stack

vProj1 :: Val -> Val
vProj1 (VTcons t u)    = t
vProj1 (VNe h sp)      = VNe h (SProj1 sp)
vProj1 _               = error "impossible"

vProj2 :: Val -> Val
vProj2 (VTcons t u)    = u
vProj2 (VNe h sp)      = VNe h (SProj2 sp)
vProj2 _               = error "impossible"

vVar :: Ix -> Vals -> Val
vVar 0 (VDef vs v) = v
vVar 0 (VSkip vs)  = VVar (valsLen vs)
vVar x (VDef vs _) = vVar (x - 1) vs
vVar x (VSkip vs)  = vVar (x - 1) vs
vVar _ _           = error "impossible"

vMeta :: MId -> Val
vMeta m = case runLookupMeta m of
  Unsolved{} -> VMeta m
  Solved v   -> v

-- | Evaluates meta solutions until we hit the first rigid constructor or
--   unsolved head variable.
force :: Val -> Val
force = \case
  v@(VNe (HMeta m) sp) | Solved v <- runLookupMeta m ->
    force (vAppSp v sp)
  v -> v

vApp :: Val -> Val -> Icit -> Origin -> Val
vApp (VLam _ _ _ _ t) ~u i o = t u
vApp (VNe h sp)       ~u i o = VNe h (SApp sp u i o)
vApp _                 _ _ o = error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u i o)  = vApp (go sp) u i o
  go (SProj1 sp)      = vProj1 (go sp)
  go (SProj2 sp)      = vProj2 (go sp)
  go (SDown sp)       = vDown (go sp)

vStage :: StageExp -> StageExp
vStage = \case
  StageExp (SHVar x) n | Just (StageExp h n') <- runLookupStageVar x ->
    vStage (StageExp h (n + n'))
  s -> s

sExp2Lit :: StageExp -> Stage
sExp2Lit s = go 0 (vStage s) where
  go acc SZero    = acc
  go acc (SSuc s) = go (acc + 1) s
  go _   _        = error "impossible"

vPred :: HasCallStack => StageExp -> StageExp
vPred s = case vStage s of
  SSuc e         -> e
  e              -> error "impossible"

vUp :: Val -> Val
vUp = \case
  VNe h (SDown sp) -> VNe h sp
  t                -> VUp t

vDown :: Val -> Val
vDown = \case
  VUp t    -> t
  VNe h sp -> VNe h (SDown sp)
  _        -> error "impossible"

valsTail :: Vals -> Vals
valsTail = \case
  VDef vs _ -> vs
  VSkip vs  -> vs
  _         -> error "impossible"

eval :: Vals -> Tm -> Val
eval vs = go where
  go = \case
    Var x         -> vVar x vs
    Let x _ _ t u -> goBind u (go t)
    U s           -> VU (vStage s)
    Meta m        -> vMeta m
    Pi x i a b    -> VPi x i (go a) (goBind b)
    Lam x i o a t -> VLam x i o (go a) (goBind t)
    App t u i o   -> vApp (go t) (go u) i o
    Tel s         -> VTel (vStage s)
    TEmpty        -> VTEmpty
    TCons x a b   -> VTCons x (go a) (goBind b)
    Rec a         -> VRec (go a)
    Tempty        -> VTempty
    Tcons t u     -> VTcons (go t) (go u)
    Proj1 t       -> vProj1 (go t)
    Proj2 t       -> vProj2 (go t)
    Skip t        -> eval (VSkip vs) t
    Wk t          -> eval (valsTail vs) t
    Code a        -> VCode (go a)
    Up t          -> vUp (go t)
    Down t        -> vDown (go t)

  goBind t ~v = eval (VDef vs v) t

-- | Quote a beta-normal form from a `Val`.
quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m -> Meta m
            HVar x  -> Var (d - x - 1)
          goSp (SApp sp u i o)  = App (goSp sp) (go u) i o
          goSp (SProj1 sp)      = Proj1 (goSp sp)
          goSp (SProj2 sp)      = Proj2 (goSp sp)
          goSp (SDown sp)       = Down (goSp sp)
      in goSp sp

    VLam x i o a t -> Lam x i o (go a) (goBind t)
    VPi x i a b    -> Pi x i (go a) (goBind b)
    VU s           -> U (vStage s)
    VTel s         -> Tel (vStage s)
    VRec a         -> Rec (go a)
    VTEmpty        -> TEmpty
    VTCons x a as  -> TCons x (go a) (goBind as)
    VTempty        -> Tempty
    VTcons t u     -> Tcons (go t) (go u)
    VCode a        -> Code (go a)
    VUp t          -> Up (go t)

  goBind t = quote (d + 1) (t (VVar d))
