
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
import Pretty
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
        (t, a) <- inferTop emptyCxt t `catch` displayError src
        checkAll 0
        t <- pure $ zonk VNil t
        let ~nt = quote 0 $ eval VNil t
        let ~na = quote 0 a
        pure (t, nt, na)

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na) <- elab
      putStrLn $ showTopTm nt
    ["type"] -> do
      (t, nt, na) <- elab
      putStrLn $ showTopTm na
    ["elab"] -> do
      (t, nt, na) <- elab
      putStrLn $ showTopTm t

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
  "let A1 = λ x y. y in",
  "let A2 : IdTy → IdTy = choose id in",
  "let A3 = choose nil ids in",
  "let A4 = λ (x : IdTy). x x in",
  "let A5 : IdTy → IdTy = id auto in",
  "let A6 : {B} → IdTy → B → B = id auto2 in",
  "let A7 = choose id auto in",
  "let A9 : ({A} → (A → A) → List A → A) → IdTy",
  "    = λ f. f (choose id) ids in",
  "let A10 = poly id in",
  "let A11 = poly (λ x. x) in",
  "let A12 = id poly (λ x. x) in",
  "let C1 = length ids in",
  "let C2 = tail ids in",
  "let C3 : IdTy = head ids in",
  "let C4 : List IdTy = single id in",
  "let C5 = cons id ids in",
  "let C6 = cons (λ x. x) ids in",
  "let C7 = append (single inc) (single id) in",
  "let C8 : _ → IdTy = λ (g : {A} → List A → List A → A). g (single id) ids in",
  "let C9 = map poly (single id) in",
  "let C10 = map head (single ids) in",
  "let D1 = app poly id in",
  "let D2 = revapp id poly in",
  "let D3 = runST argST in",
  "let D4 = app runST argST in",
  "let D5 = revapp argST runST in",
  "let E2 =",
  "  λ (h : Int → {A} → A → A)(k : {A} → A → List A → A)(lst : List ({A} → Int → A → A)).",
  "  k (λ x. h x) lst in",
  "let E3 =",
  "  λ (r : ({A} → A → {B} → B → B) → Int). r (λ x y. y) in  ",
  "U"
  ]
