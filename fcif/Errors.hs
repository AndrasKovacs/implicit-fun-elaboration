module Errors where

import Control.Exception
import Text.Printf

import Types
import Pretty

--------------------------------------------------------------------------------

data SpineError
  = SpineNonVar
  | SpineProjection
  | NonLinearSpine Lvl
  deriving (Show, Exception)

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck
  deriving (Show, Exception)

data UnifyError
  = UnifyError Cxt Tm Tm
  | SpineError Cxt Tm Tm SpineError
  | StrengtheningError Cxt Tm Tm StrengtheningError
  deriving (Show, Exception)

data ElabError
  = UnifyErrorWhile Tm Tm UnifyError
  | NameNotInScope Name
  | ExpectedFunction Tm
  | ExpectedEx Tm
  | IcitMismatch Icit Icit
  | ExpectedType Tm

data Err = Err {
  errCxt :: Cxt,
  errErr :: ElabError,
  errPos :: Maybe SPos}

instance Show Err where
  show (Err cxt err _) =
    showError cxt err

instance Exception Err

report :: Cxt -> ElabError -> IO a
report cxt e = throwIO (Err cxt e Nothing)

-- | Rethrow an `Err` with source position attached.
addSrcPos :: SPos -> IO a -> IO a
addSrcPos p act = act `catch` \case
  Err cxt e Nothing -> throwIO (Err cxt e (Just p))
  e                 -> throwIO e


showError :: Cxt -> ElabError -> String
showError cxt = \case
  UnifyErrorWhile lhs rhs e ->
    let err1 = case e of
          UnifyError cxt lhs rhs -> printf
            ("Cannot unify\n\n" ++
             "  %s\n\n" ++
             "with\n\n" ++
             "  %s\n\n")
            (showTm cxt lhs) (showTm cxt rhs)
          StrengtheningError cxt lhs rhs e -> case e of
            ScopeError x -> printf (
              "Variable %s is out of scope in equation\n\n" ++
              "  %s =? %s\n\n")
              (lvlName cxt x) (showTm cxt lhs) (showTm cxt rhs)
            OccursCheck -> printf (
              "Meta occurs cyclically in its solution candidate in equation:\n\n" ++
              "  %s =? %s\n\n")
              (showTm cxt lhs) (showTm cxt rhs)
          SpineError cxt lhs rhs e -> case e of
            SpineNonVar -> printf (
              "Non-bound-variable value in meta spine in equation:\n\n" ++
              "  %s =? %s\n\n")
              (showTm cxt lhs) (showTm cxt rhs)
            SpineProjection ->
              "Projection in meta spine\n\n"
            NonLinearSpine x -> printf
              ("Nonlinear variable %s in meta spine in equation\n\n" ++
               "  %s =? %s\n\n")
              (lvlName cxt x)
              (showTm cxt lhs) (showTm cxt rhs)
    in err1 ++ printf
         ("while trying to unify\n\n" ++
         "  %s\n\n" ++
         "with\n\n" ++
         "  %s") (showTm cxt lhs) (showTm cxt rhs)

  NameNotInScope x ->
    "Name not in scope: " ++ x
  ExpectedFunction ty ->
    "Expected a function type, instead inferred:\n\n  " ++ showTm cxt ty
  ExpectedEx ty ->
    "Expected an existential type, instead inferred:\n\n  " ++ showTm cxt ty
  ExpectedType t ->
    "Expected a type, instead inferred type:\n\n  " ++ showTm cxt t
  IcitMismatch i i' -> printf (
    "Function icitness mismatch: expected %s, got %s.")
    (show i) (show i')
