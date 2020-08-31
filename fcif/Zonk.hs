
module Zonk where

import Types
import Evaluation
import ElabState

-- | Unfold all metas and evaluate meta-headed spines, but don't evaluate
--   anything else.
zonk :: Vals -> Tm -> Tm
zonk vs t = go t where

  goSp :: Tm -> Either Val Tm
  goSp = \case
    Meta m       -> case runLookupMeta m of
                      Solved v -> Left v
                      _        -> Right (Meta m)
    App t u ni   -> case goSp t of
                      Left t  -> Left (vApp t (eval vs u) ni)
                      Right t -> Right $! App t (go u) ni
    Check m t    -> case runLookupMeta m of
                      Checked t   -> Right $! go t
                      Unchecked{} -> goSp t
                      _           -> error "impossible"
    t            -> Right (zonk vs t)

  goBind = zonk (VSkip vs)

  go = \case
    Var x        -> Var x
    Meta m       -> case runLookupMeta m of
                      Solved v   -> quote (valsLen vs) v
                      Unsolved{} -> Meta m
                      _          -> error "impossible"
    U            -> U
    Pi x i a b   -> Pi x i (go a) (goBind b)
    App t u ni   -> case goSp t of
                      Left t  -> quote (valsLen vs) (vApp t (eval vs u) ni)
                      Right t -> App t (go u) ni
    Lam x i a t  -> Lam x i (go a) (goBind t)
    Let x a t u  -> Let x (go a) (go t) (goBind u)
    Skip t       -> Skip (goBind t)
    Check m t    -> case runLookupMeta m of
                      Checked t   -> go t
                      Unchecked{} -> go t
                      _           -> error "impossible"
