module Parser (
  iParse
)where

import Text.Parsec hiding (State)
import Text.Parsec.Indent
import Control.Monad.State (State)
import Text.Parsec.Pos (SourcePos, newPos, sourceName, sourceLine, sourceColumn)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Control.Applicative ((<$>), (<*>))
import Control.Monad (join)
import Text.Parsec.Expr
import Data.List
import Data.Char
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Type as T
import qualified AST as A
import qualified Module as M
import qualified TypeInfer as TI

-- Lexer

languageDef :: P.GenLanguageDef String st (State SourcePos)
languageDef = P.LanguageDef
  {
   P.commentStart    = P.commentStart haskellDef
  ,P.commentEnd      = P.commentEnd haskellDef
  ,P.commentLine     = P.commentLine haskellDef
  ,P.nestedComments  = P.nestedComments haskellDef
  ,P.identStart      = letter
  ,P.identLetter     = alphaNum <|> char '_' <|> char '#' <|> char '.'
  ,P.opStart         = P.opLetter languageDef
  ,P.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  ,P.reservedOpNames = P.reservedOpNames haskellDef
  ,P.reservedNames   = P.reservedNames haskellDef
  ,P.caseSensitive   = P.caseSensitive haskellDef
  }

lexer :: P.GenTokenParser String M.Module (State SourcePos)
lexer = P.makeTokenParser (languageDef)

whiteSpace     = P.whiteSpace lexer
lexeme         = P.lexeme lexer
symbol         = P.symbol lexer
parens         = P.parens lexer
braces         = P.braces lexer
brackets       = P.brackets lexer
squares        = P.squares lexer
semi           = P.semi lexer
comma          = P.comma lexer
colon          = P.colon lexer
dot            = P.dot lexer
semiSep        = P.semiSep lexer
semiSep1       = P.semiSep1 lexer
commaSep       = P.commaSep lexer
commaSep1      = P.commaSep1 lexer
charLiteral    = P.charLiteral lexer
stringLiteral  = P.stringLiteral lexer
decimal        = P.decimal lexer
hexadecimal    = P.hexadecimal lexer
octal          = P.octal lexer
natural        = P.natural lexer
integer        = P.integer lexer
float          = P.float lexer
naturalOrFloat = P.naturalOrFloat lexer
identifier     = P.identifier lexer
reserved       = P.reserved lexer
operator       = P.operator lexer
reservedOp     = P.reservedOp lexer

capIdent = do
  i@(c:_) <- identifier
  if isUpper c
  then return i
  else unexpected $ i ++ " : identifier of module, type, constructor shoulde be captial"

ident = do
  i@(c:_) <- identifier
  if not (isUpper c)
  then return i
  else unexpected $ i ++ " : identifier of module, type, constructor shoulde not be captial"


-- Parser

type IParser a = ParsecT String M.Module (State SourcePos) a

modifyModuleOrFail res =
  case res of
    Right m -> setState m
    Left s -> do
      pos <- getPosition
      error $ "Error : " ++ (show $ sourceName pos) ++ ":("
              ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos)
              ++ ")\n\n" ++ s

modDef = do
  (b, c) <- withPos $
    let f _ b _ = (b, [])
    in return f <+/> reserved "module"
      <+/> capIdent
      -- <+/> (indentParens lexer (commaSep ((\pos e-> (pos, e)) <$> getPosition <*> identifier)) <|> return [])
      <+/> reserved "where" <?> "module declare"
  endLine
  m <- getState
  setState $ foldl' (\acc (pos, n) -> M.addExport n pos acc) (M.setName b m) c
  (try (modImport <?> "import") <|> return [()])
  checkIndent
  modBody <?> "module body"
  getState

endLine = many semi

modImport = do
  block $ do
    pos <- getPosition
    (b, c) <- (try (withPos $ let f _ b _ d = (b, d)
        in (return f) <+/> reserved "import" <+/> capIdent <+/> reserved "as" <+/> capIdent)
      <|> (withPos $ let f _ b = (b, "")
        in (return f) <+/> reserved "import" <+/> capIdent))
    endLine
    m <- getState
    setState $ M.addImport b c pos m
    return ()

modBody = do
  block $ do
    (dataDecl <?> "data")
    <|> ((try funcType) <?> "declare function type")
    <|> (funcDecl <?> "define function")

dataDecl = do
  pos <- getPosition
  (b, c, e) <- withPos $ let f _ b c _ e = (b, c, e)
    in return f <+/> reservedOp "data" <+/> capIdent <+/> (many ident) <+/> reservedOp "=" <+/> (dataAlter <?> "data declare")
  endLine
  foldl'
    (\acc (n, ps, pos) -> do
      if (Set.fromList c /= TI.ftv ps)
      then error $ (show $ Set.fromList c) ++ " do not match with " ++ (show $ TI.ftv ps)
      else (do m <- acc
               modifyModuleOrFail $ M.addEnv n (if length ps == 0
                                                then T.Scheme [] (T.TCN b)
                                                else T.Scheme (Set.toList $ TI.ftv ps) (T.TFun ps (T.TCon (T.TCN b) (map T.TVar c)))) pos m
               m <- getState
               (let p = foldl' (\acc _ -> (A.EVar ("a" ++ (show $ length acc)) pos):acc) [] ps
                in modifyModuleOrFail $ M.addSource n (if length ps == 0
                                                       then A.ECon (A.CCon n []) pos
                                                       else A.EFun n p (A.ECon (A.CCon n p) pos) pos) m))
      getState
    )
    getState
    e
  m <- getState
  let ds = map (\(a, b, _) -> (T.TCon (T.TCN a) b)) e
   in modifyModuleOrFail $ M.addType b ((T.TCon (T.TCN b) (map T.TVar c)):ds) pos m
  return ()

dataConstruct = do
  (indentParens lexer dataConstruct)
  <|> try (do
      pos <- getPosition
      withPos $ let f a b = (a, b, pos)
        in return f <+/> capIdent <*/> typeDecl)

dataAlter = do
  try (do
      withPos $ let f a _ b = a:b
        in return f <+/> dataConstruct <+/> reservedOp "|" <+/> dataAlter)
  <|> (do
      (\a -> [a]) <$> dataConstruct)

simpleTypeDecl = do
  (indentParens lexer typeDecl)
  <|> try (do
             withPos $ let f a b =
                             (case a of
                               "Int" -> T.TInt
                               "Bool" -> T.TBool
                               "String" -> T.TStr
                               "Float" -> T.TFloat
                               "Double" -> T.TDouble
                               _ -> if (length b == 0)
                                    then T.TCN a
                                    else T.TCon (T.TCN a) b)
                       in return f <+/> capIdent <*/> simpleTypeDecl)
  <|> try (do 
             pos <- getPosition
             withPos $ let f a = T.TVar a
                in return f <+/> ident)

funcTypeDecl = do
  --pos <- getPosition
  withPos $ let f a _ c = T.TFun [a] c
    in return f <+/> (try (indentParens lexer typeDecl) <|> simpleTypeDecl) <+/> reservedOp "->" <+/> typeDecl

typeDecl = do
  try funcTypeDecl
  <|> simpleTypeDecl

funcDecl = do
  funcBody

funcType = do
  pos <- getPosition
  (n, t) <- withPos $ let f a _ c = (a, c)
    in (return f) <+/> ident <+/> reservedOp "::" <+/> typeDecl
  endLine
  m <- getState
  modifyModuleOrFail $ M.addEnv n (T.Scheme (Set.toList $ TI.ftv t) t) pos m
  return ()

funcBody = do
  pos <- getPosition
  (n, ps, e) <- withPos $ let f a b _ d = (a, b, d)
    in (return f) <+/> ident <+/> (many pattern) <+/> reservedOp "=" <+/> expr
  endLine
  m <- getState
  modifyModuleOrFail $ M.addSource n (A.EFun n ps e pos) m
  return ()

pattern = do
  try (indentParens lexer pattern)
  <|> try (do
        pos <- getPosition
        withPos $ let f a b = A.ECon (A.CCon a b) pos
          in return f <+/> capIdent <*/> pattern)
  <|> try (do
        pos <- getPosition
        withPos $ let f a = A.EVar a pos
          in return f <+/> ident)
  <|> try (do
        pos <- getPosition
        (\p -> A.ECon (A.CCon "()" p) pos) <$> (indentParens lexer (commaSep pattern)))
  <|> try (do
        pos <- getPosition
        (\a -> A.ELit (A.LDouble a) pos) <$> float)
  <|> (do
      pos <- getPosition
      (\a -> A.ELit (A.LInt a) pos) <$> natural)
  <|> (do
      pos <- getPosition
      (\a -> A.ELit (A.LStr a) pos) <$> stringLiteral)
  <|> (do
      pos <- getPosition
      (\p -> A.ECon (A.CCon ":" p) pos) <$> (indentParens lexer (return (\a _ c -> [a, c]) <+/> pattern <+/> reservedOp ":" <+/> pattern)))
  <|> (do
      pos <- getPosition
      (\p -> A.ECon (A.CCon "[]" p) pos) <$> (indentBrackets lexer (commaSep pattern)))

expr = buildExpressionParser table factor

table = [
  [op "*" mul AssocLeft, op "/" div AssocLeft],
  [op "+" add AssocLeft, op "-" minus AssocLeft],
  [op "||" lor AssocLeft, op "&&" land AssocLeft],
  [op ":" cons AssocRight],
  [op ">=" ge AssocLeft, op "<=" le AssocLeft,
   op ">" g AssocLeft, op "<"  l AssocLeft],
  [op "==" eq AssocLeft, op "/=" ne AssocLeft],
  [op "|>" rp AssocRight, op "<|" lp AssocLeft]
  ]
  where
    mul a b = A.EApp (A.EVar "*" (A.exprPos a)) [a, b] (A.exprPos a)
    div a b = A.EApp (A.EVar "/" (A.exprPos a)) [a, b] (A.exprPos a)
    add a b = A.EApp (A.EVar "+" (A.exprPos a)) [a, b] (A.exprPos a)
    minus a b = A.EApp (A.EVar "-" (A.exprPos a)) [a, b] (A.exprPos a)
    eq a b = A.EApp (A.EVar "==" (A.exprPos a)) [a, b] (A.exprPos a)
    ne a b = A.EApp (A.EVar "/=" (A.exprPos a)) [a, b] (A.exprPos a)
    ge a b = A.EApp (A.EVar ">=" (A.exprPos a)) [a, b] (A.exprPos a)
    le a b = A.EApp (A.EVar "<=" (A.exprPos a)) [a, b] (A.exprPos a)
    g  a b = A.EApp (A.EVar ">" (A.exprPos a)) [a, b] (A.exprPos a)
    l  a b = A.EApp (A.EVar "<" (A.exprPos a)) [a, b] (A.exprPos a)
    lor a b = A.EApp (A.EVar "||" (A.exprPos a)) [a, b] (A.exprPos a)
    land a b = A.EApp (A.EVar "&&" (A.exprPos a)) [a, b] (A.exprPos a)
    rp a b = A.EApp b [a] (A.exprPos a)
    lp a b = A.EApp a [b] (A.exprPos a)
    cons a b = A.EApp (A.EVar ":" (A.exprPos a)) [a, b] (A.exprPos a)
    op s f assoc = Infix (do{reservedOp s; return f}) assoc

factor = do
  --pos <- getPosition
  ((try funcCall)
    <|> try (indentParens lexer expr)
    <|> lambdaExpr
    <|> ifExpr
    <|> caseExpr
    <|> letExpr
    <|> tupleExpr
    <|> listExpr
    <|> simpleExpr)

lambdaExpr = do
  pos <- getPosition
  withPos $ let f _ b _ d = A.EAbs b d pos
    in return f <+/> reservedOp "\\" <+/> (many pattern) <+/> reservedOp "->" <+/> expr

ifExpr = do
  pos <- getPosition
  withPos $ let f _ b _ d _ g = A.EIf b d g pos
    in return f <+/> reserved "if" <+/> expr <+/> reserved "then" <+/> expr <+/> reserved "else" <+/> expr

letExpr = do
  pos <- getPosition
  withPos $ let f _ b _ d = A.ELet b d pos
    in return f <+/> reserved "let" <+/> letDecl <+/> reserved "in" <+/> expr

letDecl = do
  block $ withPos $ let g a _ c = (a, c)
    in return g <+/> pattern <+/> reserved "=" <+/> expr

caseExpr = do
  pos <- getPosition
  b <- withPos $ let f _ b _ = b
    in return f <+/> reserved "case" <+/> expr <+/> reserved "of"
  indented
  c <- block (do
    withPos $ let g a _ c = (a, c)
      in return g <+/> pattern <+/> reserved "->" <+/> expr
    )
  return $ A.ECase b c pos

param = do
    try (indentParens lexer expr)
    <|> lambdaExpr
    <|> ifExpr
    <|> caseExpr
    <|> letExpr
    <|> tupleExpr
    <|> listExpr
    <|> simpleExpr

funcCall = do
  pos <- getPosition
  try (withPos  $ let f a b c = A.EApp a (b:c) pos
    in return f <+/> (indentParens lexer expr) <+/> param <*/> param)
  <|> (do
      pos <- getPosition
      withPos $ let f a b c = A.EApp (A.EVar a pos) (b:c) pos
        in return f <+/> identifier <+/> param <*/> param)

tupleExpr = do
  pos <- getPosition
  (\a -> A.ECon (A.CCon "()" a) pos) <$> (indentParens lexer (commaSep expr))

listExpr = do
  pos <- getPosition
  (\a -> A.ECon (A.CCon "[]" a) pos) <$> (indentBrackets lexer (commaSep expr))

simpleExpr = do
  (do
     pos <- getPosition
     reserved "not"
     ((\e -> A.EApp (A.EVar "not" pos) [e] pos) <$> expr))
  <|> (do
        pos <- getPosition
        (try ((\a -> A.EVar a pos) <$> ident)))
  <|> (do
  	    pos <- getPosition
  	    (\a -> A.ECon (A.CCon a []) pos) <$> capIdent)
  <|> try (do
        pos <- getPosition
        (\a -> A.ELit (A.LDouble a) pos) <$> float)
  <|> (do
      pos <- getPosition
      (\a -> A.ELit (A.LInt a) pos) <$> natural)
  <|> (do
      pos <- getPosition
      (\a -> A.ELit (A.LStr a) pos) <$> stringLiteral)


parser = do
  whiteSpace
  m <- modDef
  eof
  return m

iParse s input = runIndent s $ runParserT parser M.initModule s input


