module Type.Utils.Parser where

import Text.Megaparsec ( (<|>), between, many, manyTill, Parsec, MonadParsec (eof, try) )
import Data.Void (Void)
import Data.Text (Text)

import Type.Utils.Expr (VExpr(..))
import Text.Megaparsec.Char (string, alphaNumChar, letterChar, space1, char)
import Text.Megaparsec.Char.Lexer (space)
import Data.Functor (($>), (<&>))

import qualified Type.Dunfield as Dunfield
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as Text

type Parser = Parsec Void Text

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

identifier :: Parser Text
identifier = do
  s <- letterChar
  r <- many alphaNumChar
  pure (Text.cons s (Text.pack r))

sc :: Parser ()
sc = L.space
  space1                         -- (2)
  (L.skipLineComment "//")       -- (3)
  (L.skipBlockComment "/*" "*/") -- (4)

stringLiteral :: Parser String
stringLiteral = char '\"' *> manyTill L.charLiteral (char '\"')

expr :: Parser ty -> Parser (VExpr ty)
expr tyP = sc *>
   (parens (app tyP)
   <|> EInt <$> L.decimal
   <|> EStr <$> stringLiteral
   <|> lambda tyP
   <|> Var . Text.unpack <$> identifier)

app :: Parser ty -> Parser (VExpr ty)
app tyP = do
  fst' <- expr tyP <* sc
  prodClause fst'
    <|> annClause fst'
    <|> foldl App fst' <$> many (expr tyP)
  where prodClause fst' = string "×" *> sc *> expr tyP <&> EPair fst'
        annClause fst'  = string ":" *> sc *> tyP      <&> Ann fst'

lambda :: Parser ty ->  Parser (VExpr ty)
lambda pTy = do
  string "λ" *> sc
  name <- identifier <* sc
  char '.'
  Lam (Text.unpack name) <$> app pTy

-- Parsing types for Dunfield

dunExprTy :: Parser (Dunfield.Ty 'Dunfield.Poly)
dunExprTy = dunForall
        <|> Dunfield.TyAlpha . Text.unpack <$> identifier
        <|> parens dunTy

dunForall :: Parser (Dunfield.Ty 'Dunfield.Poly)
dunForall = do
  string "∀" *> sc
  name <- identifier <* sc
  char '.' *> sc
  Dunfield.TyForall (Text.unpack name) <$> dunTy

dunTy :: Parser (Dunfield.Ty 'Dunfield.Poly)
dunTy = do
  fst' <- dunExprTy <* sc
  (string "->" *> sc *> dunTy <&> Dunfield.TyFun fst')
    <|> (string "×" *> sc *> dunTy <&> Dunfield.TyPair fst')
    <|> pure fst'

parseDunfieldExpr :: Parser (VExpr (Dunfield.Ty 'Dunfield.Poly))
parseDunfieldExpr = (try (app dunTy) <|> expr dunTy) <* eof

-- Parsing types for Simple typed bidirectional