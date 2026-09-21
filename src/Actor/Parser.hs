module Actor.Parser where

import Text.Megaparsec (Parsec, MonadParsec (lookAhead, eof), try, (<?>), parse, getSourcePos)
import Data.Void (Void)
import Actor.Ast (Actor (Actor), ActorType (ActorT), ActorClause (ActorClause), Action (..), ActorProgram, Defs (ADef, FDef))
import Ast
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Control.Applicative ( optional, Alternative (some, (<|>)) )
import Parser
import Control.Monad.Combinators.Expr (makeExprParser, Operator (InfixL))
import Control.Monad (guard)

-- Lazy way to avoid ambiguity between regular function defs
pActorIdentifier :: Parser Ident
pActorIdentifier = lexeme p
  where
    p = do
      lookAhead (char '$')
      pos <- getSourcePos
      fst <- char '$'
      str <- some (alphaNumChar <|> char '-' <|> char '_' <|> char '\'' <?> "identifier that is not a keyword: " ++ show reservedWords)
      guard (str `notElem` reservedWords)
      return $ Ident (fst:str) pos


pActorDef :: Parser Actor
pActorDef = do
    (idt, tps) <- try pActorType <?> "function signature"
    Actor idt tps <$> some (try $ pActorDefClause $ identifier idt)

pActorDefClause :: String -> Parser ActorClause
pActorDefClause iTps = L.nonIndented scn $ L.lineFold scn p
    where
        p sc' = do
            idt <- pActorIdentifier
            guard (identifier idt == iTps)

            -- Parse message, TODO if empty this could be optional
            symbol ":"
            msg <- pLexprA
            symbol "="
            sc'
            ActorClause idt msg <$> pAction

pActorType :: Parser (Ident, Maybe ActorType)
pActorType = L.nonIndented scn p
    where
        p = do
            idt <- lookAhead pActorIdentifier
            tps <- optional $ try t
            return (idt, tps)
        t = do
            pActorIdentifier
            symbol "::"
            actorType

actorType :: Parser ActorType
actorType = do
    -- Message type x In type x Out type
    symbol "Actor"
    ActorT <$> btype <*> btype <*> btype

pAction :: Parser Action
pAction = comp <?> "arrow composition"
    where
        comp = makeExprParser pAction' table
        table = [ [ InfixL (symbol ">>>" >> return Comp) ]]

pAction' :: Parser Action
pAction' = aParens <|> arr <|> first <|> second <|> send <|> spawn <|> yield <?> "action"
    where
        aParens = parens pAction
        arr = symbol "arr" >> Arr <$> pLexprA
        first = symbol "first" >> First <$> pAction
        second = symbol "second" >> Second <$> pAction
        send = symbol "send" >> return Send
        spawn = symbol "spawn" >> (Spawn <$> pActorIdentifier <*> pLexprA)
        yield = symbol "yield" >> return Yield



pActorProgram :: Parser ActorProgram
pActorProgram = some (actors <|> funs <?> "defs")
    where
        funs = FDef <$> (try pDataType <|> pFunDef <?> "function or data type")
        actors = ADef <$> pActorDef

actorProgramParser :: Parser ActorProgram
actorProgramParser = pActorProgram <* scn <* eof

-- IO

actorParseFromFile :: FilePath -> IO (Either ParserError ActorProgram)
actorParseFromFile fname =
  do input <- readFile fname
     return (parse actorProgramParser fname input)

actorParseFromString :: String -> IO (Either ParserError ActorProgram)
actorParseFromString input =
  return (parse actorProgramParser "WebForm" input)
