module Errors where

import Control.Exception
import Lens.Micro.Platform
import System.Exit
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
  errErr :: ElabError}

instance Show Err where
  show (Err cxt err) = showError cxt err

instance Exception Err

report :: Cxt -> ElabError -> IO a
report cxt e = throwIO (Err cxt e)

displayError :: String -> Err -> IO a
displayError file (Err cxt err) = do
  let SPos (SourcePos path (unPos -> linum) (unPos -> colnum)) = cxt^.pos
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n\n" (showError cxt err)
  exitSuccess

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
