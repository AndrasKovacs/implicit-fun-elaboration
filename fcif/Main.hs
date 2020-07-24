
module Main where

import Text.Printf
import Control.Exception
import System.Exit
import System.Environment

import Types
import Evaluation
import Elaboration
import Errors
import Parser
import ElabState
import Zonk

helpMsg :: String
helpMsg = unlines [
  "usage: fcif [--help|elab|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin, print elaboration output",
  "  nf     : read & elaborate expression from stdin, print its normal form",
  "  type   : read & elaborate expression from stdin, print its (normal) type"]

displayError :: String -> Err -> IO a
displayError file (Err ns err (Just (SPos (SourcePos path (unPos -> linum) (unPos -> colnum))))) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n\n" (showError ns err)
  exitSuccess
displayError file (Err _ _ Nothing) =
  error "impossible"


mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do
  let elab :: IO (Tm, Tm, Tm)
      elab = do
        reset
        (t, src) <- getTm
        (t, a, s) <- inferTopLams emptyCxt t `catch` displayError src
        solveStagesTo0
        t <- pure $ zonk VNil t
        let ~nt = quote 0 $ eval VNil t
        let ~na = quote 0 a
        pure (t, nt, na)

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na) <- elab
      putStrLn $ show nt
    ["type"] -> do
      (t, nt, na) <- elab
      putStrLn $ show na
    ["elab"] -> do
      (t, nt, na) <- elab
      putStrLn $ show t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)


test1 = unlines [
  "let id   = λ {A : ^U}(x : ^(~A)). x in",
  "let Bool = {B} → B → B → B in",
  "let true  : Bool = λ t f. t in",
  "let false : Bool = λ t f. f in",
  "let and : ^Bool → ^Bool → ^Bool = λ x y. <λ t f. (~x) ((~y) t f) t> in",
  "let List = λ A. {L} → (A → L → L) → L → L in",
  "let nil : {A} → List A = λ c n. n in",
  "let cons : {A} → A → List A → List A = λ a as c n. c a (as c n) in",
  "let foo : List Bool = cons true (cons true nil) in",
  "let foldr : {A B : ^U} → (^(~A) → ^(~B) → ^(~B)) → ^(~B) → ^(List (~A) → ~B)",
  "    = λ {A}{B} f z. <λ as. as (λ a b. ~(f <a> <b>)) (~z)> in",
  "let map : {A B : ^U} → (^(~A) → ^(~B)) → ^(List (~A) → List (~B))",
  "    = λ {A}{B} f. <λ as c n. as (λ a. c (~(f <a>))) n> in",
  "<map>"
  ]
