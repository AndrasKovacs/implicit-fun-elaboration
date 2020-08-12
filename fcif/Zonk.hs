
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
    App t u ni o   -> case goSp t of
                        Left t  -> Left (vApp t (eval vs u) ni o)
                        Right t -> Right $ App t (go u) ni o
    t            -> Right (zonk vs t)

  goBind = zonk (VSkip vs)

  go = \case
    Var x         -> Var x
    Meta m        -> case runLookupMeta m of
                       Solved v   -> quote (valsLen vs) v
                       Unsolved{} -> Meta m
    U s           -> U (vStage s)
    Pi x i a b    -> Pi x i (go a) (goBind b)
    App t u ni o  -> case goSp t of
                       Left t  -> quote (valsLen vs) (vApp t (eval vs u) ni o)
                       Right t -> App t (go u) ni o
    Lam x i o a t -> Lam x i o (go a) (goBind t)
    Let x a s t u -> Let x (go a) (vStage s) (go t) (goBind u)
    Tel s         -> Tel (vStage s)
    TEmpty        -> TEmpty
    TCons x t u   -> TCons x (go t) (goBind u)
    Rec a         -> Rec (go a)
    Tempty        -> Tempty
    Tcons t u     -> Tcons (go t) (go u)
    Proj1 t       -> Proj1 (go t)
    Proj2 t       -> Proj2 (go t)
    Skip t        -> Skip (goBind t)
    Wk t          -> Wk (zonk (valsTail vs) t)

    Code a        -> Code (go a)
    Up t          -> Up (go t)
    Down t        -> Down (go t)
