module Module(
  Module(..),
  Exports,
  Imports,
  Source,
  Env,
  initModule,
  setName,
  addExport,
  addImport,
  addType_,
  addType,
  addSource_,
  addSource,
  addEnv_,
  addEnv,
  addInitEnv
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Regex.Posix
import Text.Parsec.Pos (SourcePos, newPos, sourceName, sourceLine, sourceColumn)
import qualified Text.PrettyPrint as PP

import qualified Type as T
import qualified AST as A
import Data.List

type Exports      = Map.Map String SourcePos
type Imports      = Map.Map String (String, SourcePos)
type Types        = Map.Map String ([T.Type], SourcePos)
type Source       = Map.Map String A.Exp 
type Env          = Map.Map String (T.Scheme, SourcePos)

data Module = Module {name::String,
                      exports::Exports,
                      imports::Imports,
                      types::Types,
                      source::Source,
                      env::Env}


nullExports = Map.empty
nullImports = Map.empty
nullTypes   = Map.empty
nullSource  = Map.empty
nullEnv     = Map.empty
initModule  = Module {name = "",
                      exports = nullExports,
                      imports = nullImports,
                      types   = nullTypes,
                      source  = nullSource,
                      env     = nullEnv}
setName n m       = m{name = n}
addExport n l m   = m{exports = Map.insert n l (exports m)}
addImport n pre l m   = m{imports = Map.insert n (pre, l) (imports m)}
addType_ n t pos m    =
	let pre = m --(name m)
	    nn = prefix pre n
	    nt = prefixTypeList pre t
	in m{types   = Map.insert nn (nt, pos) (types m)}
addType n t pos m     =
	let pre = m -- (name m)
	    nn = prefix pre n
	    nt = prefixTypeList pre t
	in case Map.lookup nn (types m) of
	   Nothing -> Right m{types   = Map.insert nn (nt, pos) (types m)}
	   Just (ot, pos) -> if elem nn global_list
	   	                 then Right m
	   	                 else Left $ "data `" ++ nn ++ "\' already exists" 
	                         ++ "\n    @ " ++ (show $ sourceName pos) ++ ":("
	                         ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos)
	                         ++ ")\n\n" ++ (show ot) ++ "\n"
addSource_ n e m  =
	let pre = m -- name m
	    nn = prefix pre n
	    ne = prefixExp pre e
	in m{source  = Map.insert nn ne (source m)}
addSource n e m   =
	let pre = m -- name m
	    nn = prefix pre n
	    ne = prefixExp pre e
	in case Map.lookup nn (source m) of
	   Nothing -> Right m{source  = Map.insert nn ne (source m)}
	   Just oe -> let pos = A.exprPos oe
	           in if elem nn global_list
	           	  then Right m
	           	  else Left $ "function `" ++ nn ++ "\' already exists"
	                   ++ "\n    @ " ++ (show $ sourceName pos) ++ ":("
	                   ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos)
	                   ++ ")\n\n" ++ (show oe) ++ "\n"
addEnv_ n s pos m     =
	let pre = m -- name m
	    nn = prefix pre n
	    ns = prefixScheme pre s
	in m{env     = Map.insert nn (ns, pos) (env m)}
addEnv n s pos m      =
	let pre = m -- name m
	    nn = prefix pre n
	    ns = prefixScheme pre s
	in case Map.lookup nn (env m) of
	   Nothing -> Right m{env     = Map.insert nn (ns, pos) (env m)}
	   Just (os, pos) -> if elem nn global_list
	   	                 then Right m
	   	                 else Left $ "type `" ++ nn ++ "\' already exists"
	                             ++ "\n    @ " ++ (show $ sourceName pos) ++ ":("
	                             ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos)
	                             ++ ")\n\n" ++ (show os) ++ "\n"


sysSourcePos = newPos "" 0 0

global_list = ["[]", "()", "True", "False", "Signal", "*", "/", "+", "-", "||", "&&", "not", "liftS", "liftS2", "foldS", "main", ":"]

prefix m n =
  let pre = name m
  in if n =~ "\\."
     then Map.foldlWithKey
     	   (\acc o (a, _)->
     	     let [[n, p, c]] = (acc =~ "(.*)\\.(.*)" :: [[String]])
     	     in if a == p
     	        then o ++ "." ++ c
     	        else n
     	   )
     	   n
     	   (imports m)
     else if elem n global_list
  	      then n
  	      else pre ++ "." ++ n

addInitEnv m =
  addType_ "[]" [(T.TCon (T.TCN "[]") [T.TVar "a"]), (T.TCon (T.TCN "[]") [T.TVar "a"])] sysSourcePos $
  addType_ "Signal" [(T.TCon (T.TCN "Signal") [T.TVar "a"]), (T.TCon (T.TCN "Signal") [T.TVar "a"])] sysSourcePos $
  addEnv_ "liftS" (T.Scheme ["a", "b"] (T.translateFunType $ T.TFun [T.TFun [T.TVar "a"] (T.TVar "b"),
     (T.TCon (T.TCN "Signal") [T.TVar "a"])] (T.TCon (T.TCN "Signal") [T.TVar "b"]))) sysSourcePos $
  addEnv_ "liftS2" (T.Scheme ["a", "b", "c"] (T.translateFunType $ T.TFun [T.TFun [T.TVar "a", T.TVar "b"] (T.TVar "c"),
     (T.TCon (T.TCN "Signal") [T.TVar "a"]), (T.TCon (T.TCN "Signal") [T.TVar "b"])]
    (T.TCon (T.TCN "Signal") [T.TVar "c"]))) sysSourcePos $
  addEnv_ "foldS" (T.Scheme ["a", "b", "c"] (T.translateFunType $ T.TFun [T.TFun [T.TVar "a", T.TVar "b"] (T.TVar "c"),
     (T.TCon (T.TCN "Signal") [T.TVar "b"])] (T.TCon (T.TCN "Signal") [T.TVar "c"]))) sysSourcePos $
  addEnv_ "True" (T.Scheme [] $ T.TBool) sysSourcePos $
  addEnv_ "False" (T.Scheme [] $ T.TBool) sysSourcePos $
  addEnv_ "*" (T.Scheme ["a"] (T.translateFunType $ T.TFun [T.TVar "a", T.TVar "a"] (T.TVar "a"))) sysSourcePos $
  addEnv_ "/" (T.Scheme ["a"] (T.translateFunType $ T.TFun [T.TVar "a", T.TVar "a"] (T.TVar "a"))) sysSourcePos $
  addEnv_ "+" (T.Scheme ["a"] (T.translateFunType $ T.TFun [T.TVar "a", T.TVar "a"] (T.TVar "a"))) sysSourcePos $
  addEnv_ "-" (T.Scheme ["a"] (T.translateFunType $ T.TFun [T.TVar "a", T.TVar "a"] (T.TVar "a"))) sysSourcePos $
  addEnv_ "||" (T.Scheme [] (T.translateFunType $ T.TFun [T.TBool, T.TBool] (T.TBool))) sysSourcePos $
  addEnv_ "&&" (T.Scheme [] (T.translateFunType $ T.TFun [T.TBool, T.TBool] (T.TBool))) sysSourcePos $
  addEnv_ "not" (T.Scheme [] (T.translateFunType $ T.TFun [T.TBool] (T.TBool))) sysSourcePos $
  addEnv_ ":" (T.Scheme ["a"] (T.translateFunType $ T.TFun [T.TVar "a", T.TCon (T.TCN "[]") [T.TVar "a"]] (T.TVar "a"))) sysSourcePos m


--prefixType :: String -> T.Type -> T.Type
prefixType pre (T.TCon a b) = T.TCon (prefixType pre a) (prefixTypeList pre b)
prefixType pre (T.TCN a)  = T.TCN $ prefix pre a
prefixType pre (T.TFun a b) = T.TFun (prefixTypeList pre a) (prefixType pre b)
prefixType pre (T.TVar n) = T.TVar $ prefix pre n
prefixType pre a = a

prefixScheme pre (T.Scheme vars t) = T.Scheme (map (prefix pre) vars) (prefixType pre t)

prefixTypeList pre []       = []
prefixTypeList pre (x:ps)   = (prefixType pre x):(prefixTypeList pre ps)

prefixExp pre (A.EVar n pos) = A.EVar (prefix pre n) pos
prefixExp pre (A.ECon (A.CCon n es) pos) = A.ECon (A.CCon (prefix pre n) (prefixExpList pre es)) pos
prefixExp pre (A.EApp f ps pos) = A.EApp (prefixExp pre f) (prefixExpList pre ps) pos
prefixExp pre (A.EAbs ps e pos) = A.EAbs (prefixExpList pre ps) (prefixExp pre e) pos
prefixExp pre (A.EFun n ps e pos) = A.EFun (prefix pre n) (prefixExpList pre ps) (prefixExp pre e) pos
prefixExp pre (A.ELet ps e pos) = A.ELet (map (\(a, b)->(prefixExp pre a, prefixExp pre b)) ps) (prefixExp pre e) pos
prefixExp pre (A.EIf c a b pos) = A.EIf (prefixExp pre c) (prefixExp pre a) (prefixExp pre b) pos
prefixExp pre (A.ECase e ps pos) = A.ECase (prefixExp pre e) (map (\(a, b)->(prefixExp pre a, prefixExp pre b)) ps) pos
prefixExp pre a = a

prefixExpList pre [] = []
prefixExpList pre (x:ps) = (prefixExp pre x):(prefixExpList pre ps)

instance Show (Module) where
  showsPrec _ x = shows $ prModule x

{-
                      name::String,
                      exports::Exports,
                      imports::Imports,
                      types::Types,
                      source::Source,
                      env::Env}
                      deriving Show
-}

prModule m =
  PP.text ("module " ++ (name m) ++ " where\n\n") PP.<>
  {-(PP.hcat (Map.foldlWithKey
              (\acc n (as, _) -> 
                 acc ++
                [PP.text $ "import " ++ n ++ (if as == "" then "\n\n" else (" as " ++ as ++ "\n\n"))])
              []
              (imports m))) PP.<> -}
  (PP.hcat (Map.foldlWithKey
              (\acc n (bs, _) ->
                let (h:h':l) = bs
                 in if n == "[]"
                    then acc
                    else acc ++ [PP.text $ "data " ++ (show h) ++ " = " ++
                               (foldl' (\acc d -> acc ++ " | " ++ (show d)) (show h') l) ++ "\n\n"]
              )
              []
              (types m))) PP.<>
  (PP.hcat (Map.foldlWithKey
              (\acc n s ->
                 acc ++ (case Map.lookup n (env m) of
                   Nothing -> []
                   Just (t, _) -> [PP.text $ n ++ " :: "++ (show t) ++ "\n"])
                  ++ [(PP.text $ show s ++ "\n\n")]
              )
              []
              (source m)))