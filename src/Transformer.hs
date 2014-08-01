module Transformer where

import qualified Module as M
import qualified Type as T
import qualified AST as A
import qualified Data.Map as Map
import Data.List
import Text.Regex.Posix
import Data.Char

replace a b [] = []
replace a b s@(x:xs) =
  if a == x
  then b ++ xs
  else s

hsName n =
  if n =~ "\\."
  then let [[m, p, c]] = (n =~ "(.*)\\.(.*)" :: [[String]])
        in replace '.' "__" $ c ++ "__" ++ p 
  else n

isCap (x:_) = isUpper x

transform2hs m = 
  "module " ++ (M.name m) ++ " where\n\n" ++
  Map.foldlWithKey
    (\acc n (h:h':l, _) ->
    	let (T.TCon (T.TCN d) ts) = h
    	    (T.TCon (T.TCN fd) fts) = h'
    	in if d == "[]"
    	   then acc
    	   else acc ++ "\n\n" ++
    	        "data " ++ (hsName d) ++ " " ++ (type2hsList ts) ++ "=\n" ++
                  foldl'
                    (\acc (T.TCon (T.TCN d) ts) ->
                  	  acc ++ "  | " ++ (hsName d) ++ " " ++ (type2hsList ts) ++ "\n"
                    )
                    ("  " ++ (hsName fd) ++ " " ++ (type2hsList fts) ++ "\n")
                    l
    )
    ""
    (M.types m) ++
  Map.foldlWithKey
    (\acc n s ->
      if isCap $ hsName n
      then acc
    	else acc ++ "\n\n" ++
    	     (case Map.lookup n (M.env m) of
    	     	Nothing -> ""
    	     	Just ((T.Scheme _ t), _) -> (hsName n) ++ " :: " ++ (type2hs t) ++ "\n") ++
    	     (exp2hs s)
    )
    ""
    (M.source m)

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