
module Main where

import Text.Printf
import Text.Read (readEither)
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
  "usage: fcif [--help|elab [STAGE]|nf|type]",
  "  --help       : Display this message.",
  "  elab [STAGE] : Read & elaborate expression from stdin, print elaboration output.",
  "                 The optional STAGE argument is a positive number, its default",
  "                 value is 1. Elaboration evaluates all code at stage STAGE or higher.",
  "                 With the default STAGE=1, all staged computation runs. STAGE=0 is",
  "                 the same as computing the normal form.",
  "  nf           : Read & elaborate expression from stdin, print its normal form.",
  "  type         : Read & elaborate expression from stdin, print its (normal) type."]

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
  let elab :: Stage -> IO (Tm, Tm, Tm)
      elab s' = do
        reset
        (t, src) <- getTm
        (t, a, s) <- inferTopLams emptyCxt t `catch` displayError src
        solveStagesTo0
        s <- case vStage s of SLit s -> pure s
                              _      -> error "impossible"
        t <- pure $ zonk VNil t
        t <- pure $ stage s' s t
        let ~nt = quote 0 $ eval VNil t
        let ~na = quote 0 a
        pure (t, nt, na)

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na) <- elab 1
      putStrLn $ show nt
    ["type"] -> do
      (t, nt, na) <- elab 1
      putStrLn $ show na
    "elab":rest -> do
      case rest of
        [] -> do
          (t, nt, na) <- elab 1
          putStrLn $ show t
        [s] | Right s' <- readEither s, 0 <= s' -> do
          (t, nt, na) <- elab s'
          putStrLn $ show t
        _ ->
          putStrLn helpMsg
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: [String] -> String -> IO ()
main' args src = mainWith (pure args) ((,src) <$> parseString src)


test1 = unlines [
  "λ (Bool  : U 0)",
  "  (true  : Bool)",
  "  (false : Bool)",
  "  (case  : {A} → Bool → A → A → A)",
  "  (List  : U 0 → U 0)",
  "  (nil   : {A} → List A)",
  "  (cons  : {A} → A → List A → List A)",
  "  (foldr : {A B} → (A → B → B) → B → List A → B)",

  "  (Nat₀  : U 0)",
  "  (zero₀ : Nat₀)",
  "  (suc₀  : Nat₀ → Nat₀)",
  "  (rec₀  : {A} → A → (A → A) → Nat₀ → A)",
  "  (mul₀  : Nat₀ → Nat₀ → Nat₀)",
  "  (add₀  : Nat₀ → Nat₀ → Nat₀).",

  "let Nat₁ : U 1 = (N : U 1) → N → (N → N) → N in",
  "let zero₁ : Nat₁ = λ _ z s. z in",
  "let suc₁ : Nat₁ → Nat₁ = λ a _ z s. s (a _ z s) in",
  "let add₁ : Nat₁ → Nat₁ → Nat₁ = λ a b N z s. a N (b N z s) s in",
  "let n₁5 : Nat₁ = λ _ z s. s (s (s (s (s z)))) in",
  "let n₁10 = add₁ n₁5 n₁5 in",

  "let n₀5 = suc₀ (suc₀ (suc₀ (suc₀ (suc₀ zero₀)))) in",
  "let n₀10 = add₀ n₀5 n₀5 in",

  "let List₁ : U 1 → U 1 = λ A. (L : U 1) → (A → L → L) → L → L in",
  "let nil₁ : {A} → List₁ A = λ _ c n. n in",
  "let cons₁ : {A} → A → List₁ A → List₁ A = λ a as L c n. c a (as L c n) in",

  "let Pair : U 1 -> U 1 -> U 1 = λ A B. (P : U 1) → (A → B → P) → P in",
  "let pair : {A B} → A → B → Pair A B = λ a b P p. p a b in",
  "let fst : {A B} → Pair A B → A = λ p. p _ (λ a b. a) in",
  "let snd : {A B} → Pair A B → B = λ p. p _ (λ a b. b) in",

  "let inlCase : {A} → ^Bool → ^[A] → ^[A] → ^[A]",
  "    = λ b t f. <case [b] [t] [f]> in",

  "let id : {A} → ^[A] → ^[A] = λ x. x in",

  "let test = [id <n₀10>] in",
  "let test = λ b n. [inlCase <b> <add₀ n n₀10> <n>] in",

  "let map : {A B } → (^[A] → ^[B]) → ^(List [A] → List [B])",
  "    = λ {A}{B} f. <foldr (λ a bs. cons [f <a>] bs) nil> in",

  "let not : ^Bool → ^Bool = λ b. inlCase b <false> <true> in",

  "let mapNot = [map not] in",

  "let exp₀ : Nat₀ → Nat₀ → Nat₀ = λ a b. rec₀ (suc₀ zero₀) (mul₀ b) a in",

  "let exp₁ : Nat₁ → ^Nat₀ → ^Nat₀",
  "    = λ a b. a _ <suc₀ zero₀> (λ n. <mul₀ [b] [n]>) in",

  "let exp5 = λ n. [exp₁ n₁5 <n>] in",

  "let lower : Nat₁ → ^Nat₀ = λ n. n _ <zero₀> (λ x. <suc₀ [x]>) in",

  -- "let upto : Nat₁ → List₁ Nat₁ = λ n.
  -- "   n _ (λ n. cons₁ n nil₁)

  "let expSum : List₁ (^Nat₀) → ^Nat₀",
  "    = λ ns. ns (List₁ (^Nat₀) → ^Nat₀)",
  "               (λ n hyp xs. <let x = [n] in [hyp (cons₁ <x> xs)]>)",
  "               (λ xs. xs _ (λ n res. <add₀ [n] [res]>) <zero₀>)",
  "               nil₁ in",

  "let test = [expSum (cons₁ <n₀5> (cons₁ <add₀ n₀5 n₀10> nil₁))] in",


  "U 0"

  ]

elabStage :: Int
elabStage = 1
