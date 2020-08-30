
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
        (t, a) <- inferTopLams emptyCxt t `catch` displayError src
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


test = unlines [
  "λ (List   : U → U)",
  "  (Bool   : U)",
  "  (ST     : U → U → U)",
  "  (Pair   : U → U → U)",
  "  (pair   : {A B} → A → B → Pair A B)",
  "  (true   : Bool)",
  "  (Int    : U)",
  "  (zero   : Int)",
  "  (inc    : Int → Int)",
  "  (head   : {A} → List A → A)",
  "  (tail   : {A} → List A → List A)",
  "  (nil    : {A} → List A)",
  "  (cons   : {A} → A → List A → List A)",
  "  (append : {A} → List A → List A → List A)",
  "  (length : {A} → List A → Int)",
  "  (map    : {A B} → (A → B) → List A → List B)",
  "  (runST  : {A} → ({S} → ST S A) → A)",
  "  (argST  : {S} → ST S Int).",
  "let the    : (A : U) → A → A         = λ A a. a in",
  "let const  : {A B} → A → B → A       = λ x y. x in",
  "let IdTy   : U                       = {A} → A → A in",
  "let single : {A} → A → List A        = λ a. cons a nil in",
  "let id     : {A} → A → A             = λ a. a in",
  "let ids    : List IdTy               = nil in",
  "let app    : {A B} → (A → B) → A → B = id in",
  "let revapp : {A B} → A → (A → B) → B = λ x f. f x in",
  "let poly   : IdTy → Pair Int Bool    = λ f. pair (f zero) (f true) in",
  "let choose : {A} → A → A → A         = const in",
  "let auto   : IdTy → IdTy             = id in",
  "let auto2  : {B} → IdTy → B → B      = λ _ b. b in",
  "U"
  ]
