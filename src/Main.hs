
module Main where

import Control.Exception
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

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do
  let elab :: IO (Tm, Tm, Tm)
      elab = do
        reset
        (t, src) <- getTm
        (t, a) <- inferTop emptyCxt t `catch` displayError src
        checkAll 0 `catch` displayError src
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

test2 = unlines [
  "let foo = length U in",
  "U"
  ]

test = unlines [

  -- Church natural numbers. We use these instead of postulating them
  -- because we want some Nat computation for defining Vec functions.
  "let Nat : U = (N : U) → (N → N) → N → N in",
  "let zero : Nat = λ N s z. z in",
  "let suc : Nat → Nat = λ a N s z. s (a N s z) in",
  "let add : Nat → Nat → Nat = λ a b N s z. a N s (b N s z) in",

  -- postulate Bool, Vec, Pair
  "λ (Bool    : U)",
  "  (true    : Bool)",
  "  (false   : Bool)",
  "  (Pair    : U → U → U)",
  "  (pair    : {A B} → A → B → Pair A B)",

  "  (Vec   : U → Nat → U)",
  "  (vnil  : {A} → Vec A zero)",
  "  (vcons : {A n} → A → Vec A n → Vec A (suc n))",
  "  (vfoldr : {A}{B : Nat → U}(f : {n} → A → B n → B (suc n))(n : B zero)",
  "            → {n} → Vec A n → B n).",

  -- Define List in terms of Vec.
  -- List functions are usually definable as eta-expansions of Vec functions,
  -- thanks to ∃ elaboration.
  "let List : U → U = λ A. ∃ n. Vec A n in",
  "let nil : {A} → List A = vnil in",
  "let cons : {A} → A → List A → List A = λ a as. vcons a as in",
  "let foldr : {A B} → (A → B → B) → B → List A → B",
  "  = λ f z as. vfoldr f z as in",

  "let single : {A} → A → List A = λ a. cons a nil in",

  "let vappend : {A n m} → Vec A n → Vec A m → Vec A (add n m)",
  "  = λ {A}{n}{m} xs ys.",
  "      vfoldr {_} {λ n. Vec A (add n m)} vcons ys xs in",

  "let append : {A} → List A → List A → List A",
  "  = λ xs ys. vappend xs ys in",

  "let v1 = vcons zero (vcons (suc zero) vnil) in",
  "let l1 = cons zero (cons zero (cons zero nil)) in",
  "let l2 : List _ = append l1 l1 in",

  -- "heterogeneous list"
  "let l3 : List (∃ A : U. A) = cons U (cons zero (cons suc nil)) in",

  "let l3b : List (∃ A. A) = cons (cons true nil) nil in",

  -- mixed ∀∃ inside list
  "let l4 : List ({A} → ∃ n. Vec A n) = cons nil (cons nil nil) in",

  -- postulate more stuff
  "λ (NatInd : (P : Nat → U) → ({n} → P n → P (suc n)) → P zero → (n : Nat) → P n)",
  "  (head : {A} → List A → A)",
  "  (tail : {A} → List A → List A).",

  "let vreplicate : (n : Nat) → {A} → A → Vec A n",
  "  = λ n {A} a. NatInd (λ n. Vec A n) (vcons a) vnil n in",

  "let replicate : Nat → {A} → A → List A",
  "  = λ n a. vreplicate n a in",

  "let vmap : {A B n} → (A → B) → Vec A n → Vec B n",
  "  = λ {A}{B}{n} f as. vfoldr {_}{λ n. Vec B n}",
  "                             (λ a bs. vcons (f a) bs) nil as in",

  "let map : {A B} → (A → B) → List A → List B",
  "  = λ f as. vmap f as in",

  "let length : {A} → List A → Nat",
  "  = λ as. fst as in",

  "let the    : (A : U) → A → A         = λ A a. a in",
  "let const  : {A B} → A → B → A       = λ x y. x in",
  "let IdTy   : U                       = {A} → A → A in",
  "let single : {A} → A → List A        = λ a. cons a nil in",
  "let id     : {A} → A → A             = λ a. a in",
  "let ids    : List IdTy               = nil in",
  "let app    : {A B} → (A → B) → A → B = id in",
  "let revapp : {A B} → A → (A → B) → B = λ x f. f x in",
  "let poly   : IdTy → Pair Nat Bool    = λ f. pair (f zero) (f true) in",
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

  "let C7 = append (single suc) (single id) in",
  "let C8 : _ → IdTy = λ (g : {A} → List A → List A → A). g (single id) ids in",
  "let C9 = map poly (single id) in",
  "let C10 = map head (single ids) in",

  "let D1 = app poly id in",
  "let D2 = revapp id poly in",

  "let E2 =",
  "  λ (h : Nat → {A} → A → A)(k : {A} → A → List A → A)(lst : List ({A} → Nat → A → A)).",
  "  k (λ x. h x) lst in",
  "let E3 =",
  "  λ (r : ({A} → A → {B} → B → B) → Nat). r (λ x y. y) in  ",

  "U"

  ]
