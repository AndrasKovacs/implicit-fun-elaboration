
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
  Unsolved{} -> VMeta m
  Solved v   -> v
  _          -> error "impossible"

-- | Evaluates meta solutions until we hit the first rigid constructor or
--   unsolved head variable. Does not force the spine of a neutral value.
force :: Val -> Val
force = \case
  v@(VNe (HMeta m) sp) -> case runLookupMeta m of
    Unsolved{} -> v
    Solved v   -> force (vAppSp v sp)
    _          -> error "impossible"
  v             -> v

-- | Force a spine, computing telescope applications where possible.
forceSp :: Spine -> Spine
forceSp sp =
  -- This is a cheeky hack, the point is that (VVar (-1)) blocks computation, and
  -- we get back the new spine.  We use (-1) in order to make the hack clear in
  -- potential debugging situations.
  case vAppSp (VVar (-1)) sp of
    VNe _ sp -> sp
    _        -> error "impossible"

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ _ t)  ~u i = t u
vApp (VNe h sp)      ~u i = VNe h (SApp sp u i)
vApp _                _ _ = error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp h = go where
  go SNil             = h
  go (SApp sp u i)    = vApp (go sp) u i

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
    Skip t       -> eval (VSkip vs) t

  goBind t x = eval (VDef vs x) t

-- | Quote a beta-normal form from a `Val`.
quote :: Lvl -> Val -> Tm
quote d = go where

  go v = case force v of
    VNe h sp ->
      let goSp SNil = case h of
            HMeta m -> Meta m
            HVar x  -> Var (d - x - 1)
          goSp (SApp sp u i)    = App (goSp sp) (go u) i
      in goSp (forceSp sp)

    VLam x i a t  -> Lam x i (go a) (goBind t)
    VPi x i a b   -> Pi x i (go a) (goBind b)
    VU            -> U

  goBind t = quote (d + 1) (t (VVar d))
