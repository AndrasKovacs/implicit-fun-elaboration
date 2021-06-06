
module Main where

import Control.Exception
import Control.Monad
import Data.IORef
import Data.Void
import System.Environment
import System.Exit
import Text.Printf

import Text.Megaparsec
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import ElabState
import Elaboration
import Errors
import Evaluation
import Parser
import Pretty
import Staging
import Types
import Zonk


-- Option parsing
--------------------------------------------------------------------------------

data Cmd = Elab Stage | Type | Nf | Help
  deriving Show

data Opts = Opts {_cmd :: Cmd, _showInserts :: Bool}
  deriving Show

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 empty empty

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
decimal  = lexeme L.decimal

pStage :: Parser Stage
pStage = (do
  n <- decimal
  when (n < 0) $
    fail "Stage argument must be a positive number."
  pure n) <|> pure 1

pCmd :: Parser Cmd
pCmd =
      (Help <$ symbol "--help")
  <|> (Type <$ symbol "type")
  <|> (Nf   <$ symbol "nf")
  <|> (Elab <$> (symbol "elab" *> pStage))

pOpts :: Parser Opts
pOpts = Opts
  <$> pCmd
  <*> ((True <$ symbol "--show-insertions") <|> pure False)
  <*  eof

parseOpts :: String -> IO Opts
parseOpts src =
  case parse pOpts "" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      putStrLn helpMsg
      exitSuccess
    Right t ->
      pure t

--------------------------------------------------------------------------------

helpMsg :: String
helpMsg = unlines [
  "usage: mstt [--help] COMMAND [--show-insertions]",
  "  mstt always reads an expression from standard input. Thus, you can use e.g.",
  "  \"cat file.mstt | mstt COMMAND\" as a way of processing \"file.mstt\".",
  "",
  "Options:",
  "  --help            : Display this message.",
  "  --show-insertions : Enable printing inserted implicit lambdas and applications. This",
  "                      makes the displayed output more explicit, and may significantly increase",
  "                      its size.",
  "",
  "Commands:",
  "  elab [STAGE]      : Read and elaborate expression from stdin, print elaboration output.",
  "                      The optional STAGE argument is a positive number, its default",
  "                      value is 1. Elaboration evaluates all code at stage STAGE or higher.",
  "                      With the default STAGE=1, all staged computation runs. STAGE=0 is",
  "                      the same as computing the normal form.",
  "  nf                : Read & elaborate expression from stdin, print its normal form.",
  "  type              : Read & elaborate expression from stdin, print its (normal) type."
  ]


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

mainWith :: IO Opts -> IO (Raw, String) -> IO ()
mainWith getOpts getTm = do

  let elab :: Stage -> IO (Tm, Tm, Tm)
      elab s' = do
        (t, src) <- getTm
        (t, a, s) <- inferTop emptyCxt t `catch` displayError src
        solveStagesTo0
        s <- pure $ sExp2Lit s
        t <- pure $ zonk VNil t
        t <- pure $ stage s' s t
        let ~nt = quote 0 $ eval VNil t
        let ~na = quote 0 a
        pure (t, nt, na)

  Opts cmd ins <- getOpts
  writeIORef showInsertions ins
  case cmd of
    Help ->
      putStrLn helpMsg
    Nf -> do
      (t, nt, na) <- elab 1
      putStrLn $ showTopTm nt
    Type -> do
      (t, nt, na) <- elab 1
      putStrLn $ showTopTm na
    Elab s -> do
      (t, nt, na) <- elab s
      putStrLn $ showTopTm t

main :: IO ()
main = mainWith (parseOpts =<< (unwords <$> getArgs)) parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' args src = mainWith (parseOpts args) ((,src) <$> parseString src)

test2 = unlines [
  "λ (x : U 0) (x : U 0) . x"
  ]


test1 = unlines [
  "λ (Bool  : U 0)",
  "  (true  : Bool)",
  "  (false : Bool)",
  "  (case  : {A : U} → Bool → A → A → A)",
  "  (List  : U 0 → U 0)",
  "  (nil   : {A : U 0} → List A)",
  "  (cons  : {A : U 0} → A → List A → List A)",
  "  (foldr : {A B : U 0} → (A → B → B) → B → List A → B)",

  "  (Nat₀  : U 0)",
  "  (zero₀ : Nat₀)",
  "  (suc₀  : Nat₀ → Nat₀)",
  "  (rec₀  : {A : U 0} → A → (A → A) → Nat₀ → A)",
  "  (mul₀  : Nat₀ → Nat₀ → Nat₀)",
  "  (add₀  : Nat₀ → Nat₀ → Nat₀).",

  "let test : List (U 0) = nil in",

  "let id : {A : ^U} → A → A = λ x. x in",

  "let id0 : {A : U 0} → A → A = λ x. x in",
  "let kek = id0 U in",

  "let const : {A B : ^U} → A → B → A = λ x y. x in",

  "let comp : {A B C: ^U} → (B → C) → (A → B) → A → C",
  "    = λ f g x. f (g x) in",

  "let ap : {A B: ^U} → (A → B) → A → B",
  "   = λ f x. f x in",

  "let foo : Nat₀ → Nat₀ = ap (comp suc₀) (comp suc₀ id) in",

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

  "let inlCase : {A : ^U} → Bool → A → A → A",
  "    = case in",

  "let test : Nat₀ = id n₀10 in",
  "let test : Bool → Nat₀ → Nat₀ = λ b n. inlCase b (add₀ n n₀10) n in",

  "let map : {A B : ^U} → (^A → ^B) → ^(List A) → ^(List B)",
  "    = λ {A}{B} f. foldr (λ a. cons (f a)) nil in",

  "let not : ^Bool → ^Bool = λ b. case b false true in",

  "let mapNot : List Bool → List Bool = map not in",

  "let exp₀ : Nat₀ → Nat₀ → Nat₀ = λ a b. rec₀ (suc₀ zero₀) (mul₀ b) a in",

  "let exp₁ : Nat₁ → Nat₀ → Nat₀",
  "    = λ a b. a _ (suc₀ zero₀) (λ n. mul₀ n b) in",

  "let exp5 : Nat₀ → Nat₀ = exp₁ n₁5 in",

  "let lower : Nat₁ → Nat₀ = λ n. n _ zero₀ suc₀ in",

  "let upto : Nat₁ → List₁ Nat₁",
  "    = λ n. n _ (λ acc. cons₁ acc nil₁) (λ hyp acc. hyp (suc₁ acc)) zero₁ in",

  "let expSum : List₁ Nat₀ → Nat₀",
  "    = λ ns. ns (List₁ Nat₀ → Nat₀)",
  "               (λ n hyp xs. <let x = [n] in hyp (cons₁ x xs)>)",
  "               (λ xs. xs _ add₀ zero₀)",
  "               nil₁ in",

  "let map₁ : {A B} → (A → B) → List₁ A → List₁ B",
  "  = λ f as. as _ (λ a. cons₁ (f  a)) nil₁ in",

  "let test : Nat₀ = expSum (cons₁ n₀5 (cons₁ (add₀ n₀5 n₀10) nil₁)) in",

  "let foo : Nat₀ = lower (add₁ n₁5 (let x : Nat₀ = zero₀ in n₁5)) in",

  "U 0"
  ]
