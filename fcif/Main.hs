
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
import Staging

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
        s <- case vStage s of SLit s -> pure s
                              _      -> error "impossible"
        t <- pure $ zonk VNil t
        t <- pure $ stage 1 s t
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
  "λ (Bool  : U)",
  "  (true  : Bool)",
  "  (false : Bool)",
  "  (case  : {A} → Bool → A → A → A)",
  "  (List  : U → U)",
  "  (nil   : {A} → List A)",
  "  (cons  : {A} → A → List A → List A)",
  "  (foldr : {A B} → (A → B → B) → B → List A → B).",

  "let map : {A B : ^U} → (^(~A) → ^(~B)) → ^(List (~A) → List (~B))",
  "    = λ {A}{B} f. <foldr (λ a. cons (~(f <a>))) nil> in",

  "map"
  ]
