
module Evaluation where

import Types
import ElabState

vVar :: Ix -> Vals -> Val
vVar 0 (VDef vs v) = v
vVar 0 (VSkip vs)  = VVar (valsLen vs)
vVar x (VDef vs _) = vVar (x - 1) vs
vVar x (VSkip vs)  = vVar (x - 1) vs
vVar _ _           = error "impossible"

vMeta :: MId -> Val
vMeta m = case runLookupMeta m of
  Solved v       -> v
  Unsolved{}     -> VMeta m
  _              -> error "impossible"

-- | Evaluates meta solutions until we hit the first rigid constructor or
--   unsolved head variable. Does not force the spine of a neutral value.
force :: Val -> Val
force = \case
  VNe (HMeta m) sp | Solved v <- runLookupMeta m ->
    force (vAppSp v sp)
  v -> v

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ _ t)  ~u i = t u
vApp (VNe h sp)      ~u i = VNe h (SApp sp u i)
vApp _                _ _ = error "impossible"

vProj1 :: Val -> Val
vProj1 (VPair t u) = t
vProj1 (VNe h sp)  = VNe h (SProj1 sp)
vProj1 _           = error "impossible"

vProj2 :: Val -> Val
vProj2 (VPair t u) = u
vProj2 (VNe h sp)  = VNe h (SProj2 sp)
vProj2 _           = error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp ~h = go where
  go SNil             = h
  go (SApp sp u i)    = vApp (go sp) u i
  go (SProj1 sp)      = vProj1 (go sp)
  go (SProj2 sp)      = vProj2 (go sp)

eval :: Vals -> Tm -> Val
eval vs = go where
  go = \case
    Var x        -> vVar x vs
    Let x _ t u  -> goBind u (go t)
    U            -> VU
    Meta m       -> vMeta m
    Pi x i a b   -> VPi x i (go a) (goBind b)
    Lam x i a t  -> VLam x i (go a) (goBind t)
    App t u i    -> vApp (go t) (go u) i
    Ex x a b     -> VEx x (go a) (goBind b)
    Pair t u     -> VPair (go t) (go u)
    Proj1 t      -> vProj1 (go t)
    Proj2 t      -> vProj2 (go t)
    Skip t       -> eval (VSkip vs) t
    Check _ t    -> eval vs t

  goBind t x = eval (VDef vs x) t

-- | Quote a beta-normal form from a `Val`.
quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m -> Meta m
            HVar x  -> Var (d - x - 1)
          goSp (SApp sp u i) = App (goSp sp) (go u) i
          goSp (SProj1 sp)   = Proj1 (goSp sp)
          goSp (SProj2 sp)   = Proj2 (goSp sp)
      in goSp sp

    VLam x i a t  -> Lam x i (go a) (goBind t)
    VPi x i a b   -> Pi x i (go a) (goBind b)
    VEx x a b     -> Ex x (go a) (goBind b)
    VPair t u     -> Pair (go t) (go u)
    VU            -> U

  goBind t = quote (d + 1) (t (VVar d))
