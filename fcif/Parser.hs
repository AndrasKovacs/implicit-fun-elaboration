
module Parser (parseString , parseStdin) where

import Data.Char
import Data.Foldable
import Data.Void
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Types

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> (SPos <$> getSourcePos) <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
braces p = char '{' *> p <* char '}'
pArrow   = symbol "→" <|> symbol "->"
pBind    = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x =
  x == "let" || x == "in" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = do
  o <- getOffset
  x <- try (takeWhile1P Nothing isAlphaNum <* ws)
  if keyword x then do
    setOffset o
    fail "unexpected keyword, expected an identifier"
  else
    pure x

pAtom :: Parser Raw
pAtom  =
      withPos (    (RVar  <$> pIdent)
               <|> (RU    <$  char 'U')
               <|> (RHole <$  char '_'))
  <|> parens pTm

pArg :: Parser (Icit, Raw)
pArg =
      ((Impl,) <$> (char '{' *> pTm <* char '}'))
  <|> ((Expl,) <$> pAtom)

pSpine :: Parser Raw
pSpine = do
  h    <- pAtom
  args <- many pArg
  pure $ foldl' (\t (i, u) -> RApp t u i) h args

pLamBinder :: Parser (Name, Maybe Raw, Icit)
pLamBinder =
      ((,Nothing,Expl) <$> pBind)
  <|> parens ((,,Expl) <$> pBind <*> optional (char ':' *> pTm))
  <|> (braces ((,,Impl) <$> pBind <*> optional (char ':' *> pTm)))

pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (\(x, a, ni) t -> RLam x a ni t) t xs

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTm) <|> pure RHole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTm))

pFunExp :: Parser Raw
pFunExp = do
  eitherP (try (some pPiBinder)) pSpine >>= \case
    Left dom -> do
      pArrow
      cod <- pTm
      pure $ foldr (\(xs, a, i) t -> foldr (\x -> RPi x i a) t xs) cod dom
    Right sp ->
      (pArrow *> (RPi "_" Expl sp <$> pTm)) <|> pure sp

pLet :: Parser Raw
pLet = do
  symbol "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ RLet x (maybe RHole id ann) t u

pTm :: Parser Raw
pTm = withPos (pLam <|> pLet <|> pFunExp)

pSrc :: Parser Raw
pSrc = ws *> pTm <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  src <- getContents
  t <- parseString src
  pure (t, src)
