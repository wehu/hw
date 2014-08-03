module Transformer (
  transform2hs,
  nullSignalState
) where

import qualified Module as M
import qualified Type as T
import qualified AST as A
import qualified Resolver as R
import qualified TypeInfer as TI
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import Text.Regex.Posix
import Data.Char
import Control.Monad.Error
import Control.Monad.State

import qualified Crypto.Hash.MD5 as MD5
import qualified Data.ByteString.Char8 as BSC

replace a b [] = []
replace a b s@(x:xs) =
  if elem x a
  then b ++ (replace a b xs)
  else x:(replace a b xs)

hsName n =
  if n =~ "\\."
  then let [[m, p, c]] = (n =~ "(.*)\\.(.*)" :: [[String]])
        in replace ['.'] "__" $ c ++ "__" ++ p 
  else n

isCap (x:_) = isUpper x

subStMain m =
  case Map.lookup "main" (M.source m) of
    Nothing -> Nothing
    Just e -> Just $ subSt (M.source m) e

newEnv env pats =
  foldl'
    (\env pat ->
      foldl'
        (\env v ->
          Map.delete v env
        )
        env
        (Set.toList $ TI.ftvPat pat)
    )
    env
    pats

transformLet env sets pos =
  foldl'
    (\env (pat, e) ->
      foldl'
        (\env v ->
          Map.insert v (A.ECase e [(pat, A.EVar v pos)] pos) env
        )
        env
        (Set.toList $ TI.ftvPat pat)
    )
    env
    sets

subSt :: M.Source -> A.Exp -> A.Exp
subSt env e@(A.EVar n _) =
  case Map.lookup n env of
    Nothing -> e
    Just e' -> subSt env e'
subSt env e@(A.ELit _ _) = e
subSt env e@(A.ECon (A.CCon c ps) pos) = A.ECon (A.CCon c (map (subSt env) ps)) pos
subSt env (A.EApp f ps pos) = A.EApp (subSt env f) (map (subSt env) ps) pos
subSt env (A.EAbs [] e pos) = subSt env e
subSt env (A.EAbs pats e pos) = A.EAbs pats (subSt (newEnv env pats) e) pos
subSt env (A.EFun n [] e pos) = subSt env e
subSt env (A.EFun n pats e pos) = subSt env (A.EAbs pats e pos)
subSt env e@(A.EIf _ _ _ _) = subSt env e
subSt env (A.ELet sets e pos) =
  subSt (transformLet env sets pos) e
subSt env (A.ECase e maps pos) =
  let nmaps = foldl'
                (\maps (pat, e) ->
                  maps ++ [(pat, subSt (newEnv env [pat]) e)]
                )
                []
                maps
   in A.ECase (subSt env e) nmaps pos

type SignalState = (Int, Set.Set T.Type)

nullSignalState = (0::Int, Set.singleton T.TInt)

type Transformer a = ErrorT String (StateT SignalState IO) a

transformMain m =
  case subStMain m of
    Nothing -> throwError "cannot find function main"
    Just e -> do
      res <- liftIO $ (runStateT $ runErrorT $ TI.ti TI.nullEnv e) $ R.initEnvForResolver m
      case res of
        (Right (_, _, n), _) -> node2hs n
        (Left err, _) -> throwError err
      --return n

transform2hs :: String -> M.Module -> Transformer String
transform2hs clk m = do
  c <- transformMain m
  let r = "{-# LANGUAGE FlexibleInstances #-}\n" ++
           "module " ++ (M.name m) ++ " where\n\n" ++
           defaultImports ++ "\n\n" ++
           Map.foldlWithKey
             (\acc n (h:h':l, _) ->
             	let (T.TCon (T.TCN d) ts) = h
             	    (T.TCon (T.TCN fd) fts) = h'
             	in if d == "[]" || d == "Signal" || d == "Clk"
             	   then acc
             	   else acc ++ "\n\n" ++
             	        "data " ++ (hsName d) ++ " " ++ (type2hsList ts) ++ "=\n" ++
                           (foldl'
                             (\acc (T.TCon (T.TCN d) ts) ->
                           	  acc ++ "  | " ++ (hsName d) ++ " " ++ (type2hsList ts) ++ "\n"
                             )
                             ("  " ++ (hsName fd) ++ " " ++ (type2hsList fts) ++ "\n")
                             l)  -- ++ "  deriving Show\n"
             )
             ""
             (M.types m) ++ "\n\n" ++
           {-Map.foldlWithKey
             (\acc n s ->
               if isCap $ hsName n
               then acc
             	else acc ++ "\n\n" ++
             	     (case Map.lookup n (M.env m) of
             	     	Nothing -> ""
             	     	Just ((T.Scheme _ t), _) -> (if n == "main" then "main__" else (hsName n)) ++ " :: " ++ (type2hs t) ++ "\n") ++
             	     (exp2hs s)
             )
             ""
             (M.source m) ++ "\n\n" -}
           (case Map.lookup "main" (M.env m) of
                    Nothing -> ""
                    Just ((T.Scheme _ t), _) -> "main__ :: Int -> " ++ (type2hs t) ++ "\n")
           ++ "main__ i = do\n"
           ++ "  v <- "++ c ++ "\n"
           ++ "  m <- get\n"
           ++ "  let clk = case Map.lookup \"clk\" m of\n"
           ++ "              Nothing -> (0::Int)\n"
           ++ "              Just v -> ((getSignalValue v)::Int)\n"
           ++ "   in put $ Map.insert \"clk\" (setSignalValue (clk + 1)) m\n"
           ++ "  if i < " ++ clk ++"\n"
           ++ "  then do\n"
           ++ "         liftIO $ putStrLn $ show v\n"
           ++ "         main__ (i + 1)\n"
           ++ "  else return v\n"
           ++ "\n\n"
           ++ builtIn ++ "\n\n"
   in do
        (_, ts) <- get
        let r1 = case (Set.toList ts) of
                  [] -> "\n\n"
                  [t] -> "data SignalValue = T" ++ (uniqTC t) ++ " " ++ (type2hs t) ++ "\n\n"
                  (x:xs) -> "data SignalValue = \n  " ++ (foldl' (\acc t-> acc ++ "\n  | T" ++ (uniqTC t) ++ " " ++ (type2hs t))
                             ("T" ++ (uniqTC x) ++ " " ++ (type2hs x)) xs) ++ "\n\n"
            r2 = foldl' (\acc t -> acc ++ "\ninstance SignalClass " ++ (type2hs t) ++ " where\n"
                          ++ "  getSignalValue (T" ++ (uniqTC t) ++ " i) = i\n"
                          ++ "  setSignalValue i = (T" ++ (uniqTC t) ++ " i)\n") "" (Set.toList ts)
         in return $ r ++ r1 ++ r2

uniqTC t = 
  let s = show $ MD5.hash $ BSC.pack $ type2hs t
   in replace ['\\', '\"', '&', '[', ']', '/', '^', '?', '<', '>', '.'] "_" s

defaultImports = unlines [
  "import Control.Parallel",
  "import Control.Monad.State",
  "import Control.Monad.Error",
  "import qualified Data.Map as Map"
  ]

builtIn = unlines [
  "type Signal a = ErrorT String (StateT (Map.Map String SignalValue) IO) a",
  "type Clk = Int",
  "liftS :: (a -> b) -> Signal a -> Signal b",
  "liftS f s = do",
  "  sv <- s",
  "  let v = f sv; in v `pseq` (return v)",
  "liftS2 :: (a -> b -> c) -> Signal a -> Signal b -> Signal c",
  "liftS2 f s1 s2 = do",
  "  s1v <- s1",
  "  s2v <- s2",
  "  let v = f s1v s2v; in v `pseq` (return v)",
  "foldS :: (Maybe a)-> (a -> b -> a) -> a -> Signal b -> Signal a",
  "foldS o f i s = do",
  "  sv <- s",
  "  case o of",
  "    Nothing -> let v = f i sv; in v `pseq` (return v)",
  "    Just ov -> let v = f ov sv; in v `pseq` (return v)",
  "clk :: Signal Clk",
  "clk = do",
  "  m <- get",
  "  case Map.lookup \"clk\" m of",
  "    Nothing -> return (0::Int)",
  "    Just v -> return ((getSignalValue v)::Int)",
  "clk2Int :: Clk -> Int",
  "clk2Int i = i",
  "int2Clk :: Int -> Clk",
  "int2Clk i = i",
  "main :: IO ()",
  "main = do",
  "  res <- (runStateT $ runErrorT (main__ 0)) Map.empty",
  "  case res of",
  "    (Right d, _) -> putStrLn $ show d",
  "    (Left err, _) -> putStrLn err",
  "class SignalClass a where",
  "  getSignalValue :: SignalValue -> a",
  "  setSignalValue :: a -> SignalValue"
  ]

type2hs (T.TVar n) = hsName n
type2hs T.TInt     = "Int"
type2hs T.TBool    = "Bool"
type2hs T.TFloat   = "Float"
type2hs T.TDouble  = "Double"
type2hs T.TStr     = "String"
type2hs (T.TCon (T.TCN "[]") [a]) = "[" ++ (type2hs a) ++ "]"
type2hs (T.TCon (T.TCN "()") []) = "()"
type2hs (T.TCon (T.TCN "()") (x:xs)) = "(" ++ (foldl' (\acc x -> acc ++ ", " ++ (type2hs x)) (type2hs x) xs) ++ ")"
type2hs (T.TCon a []) = type2hs a
type2hs (T.TCon a b) = "(" ++ (type2hs a) ++ " " ++ type2hsList b ++ ")"
type2hs (T.TCN a)  = hsName a
type2hs (T.TFun a b) = "(" ++ (type2hsList a) ++ " -> " ++ (type2hs b) ++ ")"

type2hsList []       = ""
type2hsList (x:ps)   = (type2hs x) ++ " " ++ (type2hsList ps)

exp2hs (A.EVar n _) = hsName n
exp2hs (A.ELit (A.LBool True) _) = "True"
exp2hs (A.ELit (A.LBool False) _) = "False"
exp2hs (A.ELit (A.LInt i) _) = show i
exp2hs (A.ELit (A.LFloat f) _) = show f
exp2hs (A.ELit (A.LDouble d) _) = show d
exp2hs (A.ELit (A.LStr s) _) = s
exp2hs (A.EAbs ps e _) = "(\\" ++ (exp2hsList ps) ++ " -> " ++ (exp2hs e) ++ ")"
exp2hs (A.EFun "main" ps e _) = "main__ " ++ (exp2hsList ps) ++ " = " ++ (exp2hs e)
exp2hs (A.EFun n ps e _) = (hsName n) ++ " " ++ (exp2hsList ps) ++ " = " ++ (exp2hs e)
exp2hs (A.ELet ps e _) = "(let " ++ (foldl' (\acc (a, b)->
                           acc ++ (exp2hs a) ++ " = " ++ (exp2hs b) ++ "; ") "" ps) ++ 
                          "in " ++ (exp2hs e) ++ ")"
exp2hs (A.EIf c a b _) = "(if " ++ (exp2hs c) ++ " then " ++ (exp2hs a) ++ " else " ++ (exp2hs b) ++ ")"
exp2hs (A.ECase e ps _) = "(case " ++ (exp2hs e) ++ " of " ++
                          (foldl' (\acc (a, b)-> acc ++ (exp2hs a) ++ " -> "
                            ++ (exp2hs b) ++ "; ") "" ps) ++ ")"
exp2hs (A.EApp (A.EVar "*" _) [a, b] _) = "(" ++ (exp2hs a) ++ " * " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "/" _) [a, b] _) = "(" ++ (exp2hs a) ++ " / " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "div" _) [a, b] _) = "(" ++ (exp2hs a) ++ " `div` " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "mod" _) [a, b] _) = "(" ++ (exp2hs a) ++ " `mod` " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "rem" _) [a, b] _) = "(" ++ (exp2hs a) ++ " `rem` " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "+" _) [a, b] _) = "(" ++ (exp2hs a) ++ " + " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "-" _) [a, b] _) = "(" ++ (exp2hs a) ++ " - " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "||" _) [a, b] _) = "(" ++ (exp2hs a) ++ " || " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "&&" _) [a, b] _) = "(" ++ (exp2hs a) ++ " && " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar ":" _) [a, b] _) = "(" ++ (exp2hs a) ++ " : " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "^" _) [a, b] _) = "(" ++ (exp2hs a) ++ " ^ " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "==" _) [a, b] _) = "(" ++ (exp2hs a) ++ " == " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "/=" _) [a, b] _) = "(" ++ (exp2hs a) ++ " /= " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar ">=" _) [a, b] _) = "(" ++ (exp2hs a) ++ " >= " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "<=" _) [a, b] _) = "(" ++ (exp2hs a) ++ " <= " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar ">" _) [a, b] _) = "(" ++ (exp2hs a) ++ " > " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "<" _) [a, b] _) = "(" ++ (exp2hs a) ++ " < " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "|>" _) [a, b] _) = "(" ++ (exp2hs a) ++ " |> " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp (A.EVar "<|" _) [a, b] _) = "(" ++ (exp2hs a) ++ " <| " ++ (exp2hs b) ++ ")"
exp2hs (A.EApp f ps _) = "(" ++ (exp2hs f) ++ " " ++ (exp2hsList ps) ++ ")"
exp2hs (A.ECon (A.CCon "[]" []) _) = "[]"
exp2hs (A.ECon (A.CCon "[]" (e:es)) _) = "[" ++ (foldl' (\acc e -> acc ++ ", " ++ (exp2hs e)) (exp2hs e) es) ++ "]"
exp2hs (A.ECon (A.CCon "()" []) _) = "()"
exp2hs (A.ECon (A.CCon "()" (e:es)) _) = "(" ++ (foldl' (\acc e -> acc ++ ", " ++ (exp2hs e)) (exp2hs e) es) ++ ")"
exp2hs (A.ECon (A.CCon n []) _) = hsName n
exp2hs (A.ECon (A.CCon n es) _) = "(" ++ (hsName n) ++ " " ++ (exp2hsList es) ++ ")"

exp2hsList [] = ""
exp2hsList (x:xs) = (exp2hs x) ++ " " ++ (exp2hsList xs)

node2hs (TI.NN e@(A.EVar _ _) _ _) = return $ exp2hs e
node2hs (TI.NN e@(A.ELit _ _) _ _) = return $ exp2hs e
node2hs (TI.NN (A.ECon (A.CCon "[]" []) _) _ _) = return "[]"
node2hs (TI.NN (A.ECon (A.CCon "[]" _) _) _ n) = do
  r <- (node2hsList n ",")
  return $ "[" ++ r ++ "]"
node2hs (TI.NN (A.ECon (A.CCon "()" []) _) _ _) = return $ "()"
node2hs (TI.NN (A.ECon (A.CCon "()" _) _) _ n) = do
  r <- (node2hsList n ",")
  return $ "(" ++ r ++ ")"
node2hs (TI.NN (A.ECon (A.CCon n []) _) _ _) = return $ hsName n
node2hs (TI.NN (A.ECon (A.CCon n _) _) _ nn) = do
  r <- (node2hsList nn " ")
  return $ "(" ++ (hsName n) ++ " " ++ r ++ ")"
node2hs (TI.NN (A.EAbs [] _ _) _ n) = node2hs n
node2hs (TI.NN (A.EAbs pats _ _) _ n) = do
  r <- (node2hs n)
  return $ "(\\" ++ (exp2hsList pats) ++ " -> " ++ r ++ ")"
node2hs (TI.NN (A.EIf _ _ _ _) _ (TI.NB [c, e1, e2])) = do
  r1 <- (node2hs c)
  r2 <- (node2hs e1)
  r3 <- (node2hs e2)
  return $ "(if " ++ r1 ++ " then " ++ r2 ++ " else " ++ r3 ++ ")"
node2hs (TI.NN (A.ECase _ maps _) _ (TI.NB (e:ns))) = 
  let nmaps = foldM
                (\maps ((pat, e), n) -> do
                  r <- (node2hs n)
                  return $ maps ++ (exp2hs pat) ++ " -> " ++ r ++ "; "
                )
                ""
                (zip maps ns)
   in do
         r1 <- (node2hs e) 
         r2 <- nmaps
         return $ "(case " ++ r1 ++ " of " ++ r2 ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "*" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " * " ++ r2 ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "/" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " / " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "/" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " / " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "div" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " `div` " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "div" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " `div` " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "mod" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " `mod` " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "mod" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " `mod` " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "rem" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " `rem` " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "rem" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " `rem` " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "+" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " + " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "+" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " + " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "-" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " - " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "-" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " - " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "||" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " || " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "||" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " || " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "&&" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " && " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "&&" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " && " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar ":" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " : " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar ":" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " : " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "^" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " ^ " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "^" _) _ _) _ (TI.NB [_, a, b]))= "(" ++ (node2hs a) ++ " ^ " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "==" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " == " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "==" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " == " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "/=" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " /= " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "/=" _) _ _) _ (TI.NB [_, a, b]))= "(" ++ (node2hs a) ++ " /= " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar ">=" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " >= " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar ">=" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " >= " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "<=" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " *<= " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "<=" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " <= " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar ">" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " > " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar ">" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " > " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "<" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " < " ++ r2 ++ ")"
--node2hs (TI.NN (A.EApp (A.EVar "<" _) _ _) _ (TI.NB [_, a, b])) = "(" ++ (node2hs a) ++ " < " ++ (node2hs b) ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "<|" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " <| " ++ r2 ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "|>" _) _ _) _ (TI.NB [_, a, b])) = do
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(" ++ r1 ++ " |> " ++ r2 ++ ")"
node2hs (TI.NN (A.EApp (A.EVar "foldS" _) _ _) (T.TCon _ [t]) (TI.NB [_, a, b, c])) = do
  (i, ts) <- get
  put $ (i + 1, Set.insert t ts)
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  r3 <- (node2hs c)
  return $ "(do m <- get; v <- (foldS (case Map.lookup \"" ++ (show i)
     ++ "\" m of Nothing -> Nothing; Just v -> Just ((getSignalValue v)::"
     ++ (type2hs t) ++ "))"
     ++ r1 ++ " " ++ r2 ++ " " ++ r3 ++ "); put $ Map.insert \"" 
     ++ (show i) ++ "\" (setSignalValue v) m; return v)"
{-node2hs (TI.NN (A.EApp (A.EVar "liftS" _) _ _) (T.TCon _ [t]) (TI.NB [_, a, b])) = do
  (i, ts) <- get
  put $ (i + 1, Set.insert t ts)
  r1 <- (node2hs a)
  r2 <- (node2hs b)
  return $ "(liftS " ++ r1 ++ " " ++ r2 ++ ")"
--}
node2hs (TI.NN (A.EApp f _ _) t n) = do
  r <- (node2hsList n " ")
  return $ "(" ++ r ++ ")"

node2hsList (TI.NN _ _ n) s = node2hs n
node2hsList (TI.NB []) s = return ""
node2hsList (TI.NB (x:xs)) s = do
  r1 <- (node2hs x)
  r2 <- (node2hsList (TI.NB xs) s)
  return $ r1 ++ s ++ r2