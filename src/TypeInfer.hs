{-
   Copyright 2014 huwei04@hotmail.com

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-}

{-# LANGUAGE FlexibleInstances #-}

module TypeInfer(
  Types(..),
  TypeEnv(..),
  Node(..),
  ftvPat,
  ti,
  typeInferState,
  nullInferred,
  runTI,
  nullTypeInferEnv
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Error
import Control.Monad.State
import Text.Parsec.Pos (sourceName, sourceLine, sourceColumn)
import Data.List
import Data.Maybe

import qualified Type as T
import qualified AST as A
import qualified Module as M

class Types a where
	ftv   :: a -> Set.Set String
	apply :: Map.Map String T.Type -> SubSt -> a -> a

type SubSt = Map.Map String T.Type

subSt s t = apply Map.empty s t
nullSubSt = Map.empty
combineSubSt s1 s2 = (Map.map (subSt s1) s2) `Map.union` s1

instance Types T.Type where
  ftv (T.TVar a) = Set.singleton a
  ftv T.TInt     = Set.empty
  ftv T.TBool    = Set.empty
  ftv T.TStr     = Set.empty
  ftv T.TFloat   = Set.empty
  ftv T.TDouble  = Set.empty
  ftv (T.TCon a b) = ftv a `Set.union` ftv b
  ftv (T.TFun a b) = ftv a `Set.union` ftv b
  ftv (T.TCN a)  = Set.empty
  apply e s (T.TVar a) =
    case Map.lookup a e of
      Nothing -> case Map.lookup a s of
                  Nothing -> T.TVar a
                  Just t  -> apply (Map.insert a t e) s t
      Just t -> t
  apply e s T.TInt  = T.TInt
  apply e s T.TBool = T.TBool
  apply e s T.TStr  = T.TStr
  apply e s T.TFloat  = T.TFloat
  apply e s T.TDouble  = T.TDouble
  apply e s (T.TCon a b) = T.TCon (apply e s a) (apply e s b)
  apply e s (T.TFun a b) = T.TFun (apply e s a) (apply e s b)
  apply e s (T.TCN a) = T.TCN a

instance Types a => Types [a] where
  ftv []       = Set.empty
  ftv (a:b)    = ftv a `Set.union` ftv b
  apply _ _ []     = []
  apply e s (a:b)  = (apply e s a):(apply e s b)

instance Types T.Scheme where
  ftv (T.Scheme vars a) = foldl' (\acc v -> Set.delete v acc) (ftv a) vars
  apply e s (T.Scheme vars a) = T.Scheme vars $ apply e (foldl' (\acc v -> Map.delete v s) s vars) a


-- 

newtype TypeEnv = TypeEnv (Map.Map String T.Scheme)

nullTypeInferEnv = TypeEnv Map.empty

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv $ Map.elems env
  apply e s (TypeEnv env) = TypeEnv $ Map.map (apply e s) env

remove (TypeEnv env) a = TypeEnv $ Map.delete a env

generalize env t =
  do ge <- getGlobalEnv
     return (T.Scheme (Set.toList $ (ftv t) `Set.difference` (ftv env) `Set.difference` (ftv ge)) t)

generalizeL env tl =
  foldl'
    (\acc n ->
        do (TypeEnv e) <- acc
           case Map.lookup n e of
             Nothing -> return $ TypeEnv e
             Just t ->
               let T.Scheme vars t' = t
               in (do nt <- generalize (TypeEnv (foldl' (\acc n -> Map.delete n acc) e tl)) t'
                      return $ TypeEnv (Map.insert n nt (Map.delete n e))))
    (return env)
    tl

type Inferred = Map.Map String Bool

nullInferred = Map.empty

data TypeInferState = TypeInferState {varc :: Int, globalEnv :: TypeEnv, source :: M.Source, inferred :: Inferred}

typeInferState c e s i = TypeInferState {varc = c, globalEnv = e, source = s, inferred = i}
initTypeInferState = typeInferState 0 nullTypeInferEnv Map.empty Map.empty

type TI a = ErrorT String (StateT TypeInferState IO) a

newTVar :: String -> TI T.Type
newTVar prefix = do
  s <- get
  put s{varc = (varc s) + 1}
  return $ T.TVar $ prefix ++ show (varc s)

getGlobalEnv :: TI TypeEnv
getGlobalEnv = do
  s <- get
  return $ globalEnv s

addGlobalEnv :: String -> T.Scheme -> TI ()
addGlobalEnv n s = do
  (TypeEnv env) <- getGlobalEnv
  s' <- get
  put s'{globalEnv = TypeEnv $ Map.insert n s env}

getSource :: TI M.Source
getSource = do
  s <- get
  return $ source s

removeSource :: String -> TI ()
removeSource n = do
  s <- get
  put s{source = Map.delete n (source s)}

getInferred :: TI (Inferred)
getInferred = do
  s <- get
  return $ inferred s

setInferred :: String -> TI ()
setInferred n = do
  s <- get
  put s{inferred = Map.insert n True (inferred s)}

instantiate (T.Scheme vars t) = do
  nvars <- mapM (\_-> newTVar "a") vars
  let s = Map.fromList (zip vars nvars)
    in return $ subSt s t

typeMismatch e t1 t2 = throwError $
                         "Error : type `" ++ (show t1) ++ "\' mismatch with type `" ++ (show t2)
                         ++ "\'\n    @ " ++ (show $ sourceName $ A.exprPos e)
                         ++ ":(" ++ (show $ sourceLine $ A.exprPos e)
                         ++ "," ++ (show $ sourceColumn $ A.exprPos e)
                         ++ ")" ++ "\n\n  in " ++ (show e) ++ "\n"

unify :: A.Exp -> T.Type -> T.Type -> TI SubSt
unify e (T.TFun [] r) t = unify e r t
unify e t (T.TFun [] r) = unify e t r
unify e (T.TFun l r) (T.TFun l' r') = do
  if length l /= length l'
  then typeMismatch e l l'
  else do s1 <- foldM
                  (\s (a, a') ->
                     do s' <- unify e (subSt s a) (subSt s a')
                        return $ s `combineSubSt` s')
                  nullSubSt
                  (zip l l')
          s2 <- unify e (subSt s1 r) (subSt s1 r')
          return $ combineSubSt s1 s2
unify e t@(T.TCon a b) t'@(T.TCon a' b') =
  if (length b) /= (length b')
  then
    typeMismatch e t t'
  else
    foldl' f (unify e a a') $ zip b b'
    where
      f acc (v, v') = do
        s1 <- acc
        s2 <- unify e (subSt s1 v) (subSt s1 v')
        return $ combineSubSt s1 s2
unify _ T.TInt T.TInt = return nullSubSt
unify _ T.TBool T.TBool = return nullSubSt
unify _ T.TFloat T.TFloat = return nullSubSt
unify _ T.TDouble T.TDouble = return nullSubSt
unify _ T.TStr T.TStr = return nullSubSt
unify e t@(T.TCN a) t'@(T.TCN a') =
  if a == a'
  then return nullSubSt
  else
    typeMismatch e t t'
unify e (T.TVar a) b = bindVar e a b
unify e a (T.TVar b) = bindVar e b a
unify e t t' = typeMismatch e t t'

bindVar e a b | T.TVar a == b =  return nullSubSt
              | a `Set.member` ftv b = typeMismatch e a b
              | otherwise = return $ Map.singleton a b

ftvPat (A.ECon (A.CCon n ps) _) = Set.unions $ map ftvPat ps
ftvPat (A.EVar n _) = Set.singleton n
ftvPat (A.ELit _ _) = Set.empty

checkPat (A.ECon (A.CCon n []) _) = Nothing
checkPat (A.ECon (A.CCon n ps) _) = foldl' (\acc p -> if isJust p || isJust acc then p else acc) Nothing $ map checkPat ps 
checkPat (A.EVar n _) = Nothing
checkPat (A.ELit _ _) = Nothing
checkPat e = Just "is not a pattern"

checkNestSignalType e t =
  if T.isNestedSignalType t
  then throwError $ "type `" ++ (show t) ++ "\' is a nested Signal Type"
                    ++ "\'\n    @ " ++ (show $ sourceName $ A.exprPos e)
                    ++ ":(" ++ (show $ sourceLine $ A.exprPos e)
                    ++ "," ++ (show $ sourceColumn $ A.exprPos e)
                     ++ ")" ++ "\n\n  in " ++ (show e) ++ "\n"
  else return t

genPat (TypeEnv env) pat =
  let c = checkPat pat
  in if isJust c then
       throwError $ fromJust c
     else 
       do
         (env', s') <- let vs = Set.toList $ ftvPat pat
                           env'' = foldl' (\acc n-> Map.delete n acc) env vs
                       in foldl'
                            (\acc n ->
                               do (env, s) <- acc
                                  nt <- newTVar "a"
                                  return $ (Map.insert n (T.Scheme [] nt) env, Map.insert n nt s)
                            )
                            (return (env'', nullSubSt))
                            vs
         (s'', t, n) <- ti (subSt s' (TypeEnv env')) pat
         return (subSt s'' $ TypeEnv env', subSt s'' t, subSt s'' n)

data Node =
  NN A.Exp T.Type Node
  | NB [Node]

nullNB = NB []

instance Types Node where
  ftv (NN _ t n) = (ftv t) `Set.union` (ftv n)
  ftv (NB ns) = ftv ns
  apply e s (NN ee t n) = NN ee (apply e s t) (apply e s n)
  apply e s (NB ns) = NB (apply e s ns)

mergeNode n1@(NN _ _ _) n2@(NN _ _ _) = NB [n1, n2]
mergeNode n1@(NN _ _ _) (NB n2) = NB (n1:n2)
mergeNode (NB n1) n2@(NN _ _ _) = NB (n1 ++ [n2])
mergeNode (NB n1) (NB n2) = NB (n1 ++ n2)


ti :: TypeEnv -> A.Exp -> TI (SubSt, T.Type, Node)
ti (TypeEnv env) e@(A.EVar a _) = do
  case Map.lookup a env of
    Nothing ->
      do (TypeEnv ge) <- getGlobalEnv
         case Map.lookup a ge of
           Nothing -> do
             (T.Scheme _ t) <- typeInfer a
             checkNestSignalType e t
             return (nullSubSt, t, NN e t nullNB)
           Just s -> do
             t <- instantiate s
             checkNestSignalType e t
             return (nullSubSt, t, NN e t nullNB)
    Just s  -> do
      t <- instantiate s
      checkNestSignalType e t
      return (nullSubSt, t, NN e t nullNB)
ti _ e@(A.ELit (A.LInt _) _) = return (nullSubSt, T.TInt, NN e T.TInt nullNB)
ti _ e@(A.ELit (A.LBool _) _) = return (nullSubSt, T.TBool, NN e T.TBool nullNB)
ti _ e@(A.ELit (A.LStr _) _) = return (nullSubSt, T.TStr, NN e T.TStr nullNB)
ti _ e@(A.ELit (A.LFloat _) _) = return (nullSubSt, T.TFloat, NN e T.TFloat nullNB)
ti _ e@(A.ELit (A.LDouble _) _) = return (nullSubSt, T.TDouble, NN e T.TDouble nullNB)
ti env e@(A.ECon (A.CCon "[]" []) _) = do
  t <- newTVar "a"
  let t' = T.TCon (T.TCN "[]") [t]
   in (do
        checkNestSignalType e t'
        return (nullSubSt, t', NN e t' nullNB))
ti env e@(A.ECon (A.CCon "[]" cs@(x:xs)) _) = do
  (s, t, n) <- foldl'
              (\acc p ->
                 do (s1, t1, n1) <- acc
                    (s2, t2, n2) <- ti (subSt s1 env) p
                    s3 <- unify e (subSt s2 t1) (subSt s2 t2)
                    return (s1 `combineSubSt` s2 `combineSubSt` s3, subSt s3 t2, subSt s3 $ mergeNode n1 n2)
              )
              (ti env x)
              xs
  let t' = subSt s $ T.TCon (T.TCN "[]") [t]
   in do
        checkNestSignalType e t'
        return (s, t', subSt s $ NN e t' n)
ti env e@(A.ECon (A.CCon c []) pos) =
  if c == "()"
  then
    let t = T.TCon (T.TCN "()") []
     in do checkNestSignalType e t
           return $ (nullSubSt, t, NN e t nullNB)
  else ti env (A.EVar c pos)
ti env e@(A.ECon (A.CCon c ps) pos) =
  if c == "()"
  then do
    (s, ts, n) <- foldl'
      (\acc e-> do
        (s1, t1, n1) <- acc
        (s2, t2, n2) <- ti (subSt s1 env) e
        return (s1 `combineSubSt` s2, subSt s2 $ t1 ++ [t2], subSt s2 $ mergeNode n1 n2)
      )
      (return (nullSubSt, [], nullNB))
      ps
    let t = subSt s $ T.TCon (T.TCN "()") ts
     in do
         checkNestSignalType e t
         return $ (s, t, subSt s $ NN e t n)
  else ti env (A.EApp (A.EVar c pos) ps pos)
ti env e@(A.EApp a [] _) =
  do nt <- newTVar "a"
     (s, t, n) <- ti env a
     s' <- unify e t (T.TFun [] nt)
     let nt' = subSt s' nt
      in do checkNestSignalType e nt'
            return (s `combineSubSt` s', nt', subSt s' $ NN e nt' (NB [n]))
ti env e@(A.EApp a ps _) =
  do nt <- newTVar "a"
     (sa, ta, na) <- ti env a
     (sp, tp, np) <- let (x:xs) = ps
                         h = (ti (subSt sa env) x) >>= (\(s, t, n) -> return (s, subSt s [t], n))
                      in foldl'
                           (\acc e ->
                              do (s1, t1, n1) <- acc
                                 (s2, t2, n2) <- ti (subSt s1 env) e
                                 return (s1 `combineSubSt` s2, subSt s2 $ t1 ++ [t2], subSt s2 $ mergeNode n1 n2))
                           h
                           xs
     s <- unify e ta (T.translateFunType $ T.TFun tp nt)
     let nt' = subSt s nt
      in do checkNestSignalType e nt'
            return (s `combineSubSt` sp `combineSubSt` sa, nt', subSt s $ NN e nt' (mergeNode na np))
ti env ae@(A.EAbs cs e pos) =
  do (env1, t1, n1) <- let (x:xs) = cs
                           h = (do
                                   (env', t, n) <- genPat env x
                                   return (env', [t], n))
                     in foldl'
                          (\acc e ->
                             do (TypeEnv env1, t1, n1) <- acc
                                (TypeEnv env2, t2, n2) <- genPat (TypeEnv env1) e
                                return (TypeEnv $ env2 `Map.union` env1, t1 ++ [t2], mergeNode n1 n2))
                          h
                          xs
     (s, t2, n2) <- ti env1 e
     let t = subSt s $ T.translateFunType $ T.TFun t1 t2
      in do checkNestSignalType ae t
            return (s, t, subSt s $ NN ae t n2)
ti env fe@(A.EFun n [] e pos) =
  do (s, t, nn) <- ti env e
     (let ft = subSt s t
      in (do --ns <- generalize (remove env n) ft
             --addGlobalEnv n ns
             checkNestSignalType fe ft
             return (s, ft, subSt s $ NN fe ft nn)))
ti env fe@(A.EFun n cs e pos) =
  do (env1, t1, n1) <- let (x:xs) = cs
                           h = (do
                                   (env', t, n) <- genPat env x
                                   return (env', [t], n))
                     in foldl'
                          (\acc e ->
                             do (TypeEnv env1, t1, n1) <- acc
                                (TypeEnv env2, t2, n2) <- genPat (TypeEnv env1) e
                                return (TypeEnv $ env2 `Map.union` env1, t1 ++ [t2], mergeNode n1 n2))
                          h
                          xs
     (s, t2, n2) <- ti env1 e
     (let ft = subSt s $ T.translateFunType $ T.TFun t1 t2
      in (do --ns <- generalize (remove env n) ft
             --addGlobalEnv n ns
             checkNestSignalType fe ft
             return (s, ft, subSt s $ NN fe ft n2)))
ti env le@(A.ELet ps e pos) = 
  do (env1, s1, t1, n1) <- let ((c, e):tl) = ps
                               th = (do
                                      (env1, t1, n1) <- genPat env c
                                      (s2, t2, n2) <- ti env e
                                      s3 <- unify le (subSt s2 t1) (subSt s2 t2)
                                      env2 <- generalizeL (subSt s3 env1) (Set.toList (ftvPat c))
                                      return (env2, s2 `combineSubSt` s3, subSt s3 t2, subSt s3 $ mergeNode n1 n2))
                           in foldl'
                                (\acc (c, e) ->
                                   do (TypeEnv env1, s1, t1, n1) <- acc
                                      (TypeEnv env2, t2, n2) <- genPat (TypeEnv env1) c
                                      (s3, t3, n3) <- ti (subSt s1 (TypeEnv env1)) e
                                      s4 <- unify le (subSt s3 t2) (subSt s3 t3)
                                      env3 <- generalizeL (subSt s4 (TypeEnv env2)) (Set.toList (ftvPat c))
                                      return (TypeEnv $ env2 `Map.union` env1,  s1 `combineSubSt` s3 `combineSubSt` s4,
                                         subSt s4 t3, subSt s4 $ mergeNode n1 $ mergeNode n2 n3)
                                )
                                th
                                tl
     (s2, t2, n2) <- ti (subSt s1 env1) e
     let t = subSt s2 t2
      in do checkNestSignalType le t
            return (s1 `combineSubSt` s2, t, subSt s2 $ NN le t (mergeNode n1 n2))
ti env e@(A.EIf c e1 e2 pos) =
  do (s1, t1, n1) <- ti env c
     if t1 /= T.TBool
     then typeMismatch e t1 T.TBool
     else do
            (s2, t2, n2) <- ti (subSt s1 env) e1
            (s3, t3, n3) <- ti (subSt s1 env) e2
            s4 <- unify e (subSt s1 t2) (subSt s1 t3)
            let t = subSt s4 t2
             in do checkNestSignalType e t
                   return (s1 `combineSubSt` s2 `combineSubSt` s3 `combineSubSt` s4, t, subSt s4 $ NN e t (mergeNode n1 $ mergeNode n2 n3))
ti env ce@(A.ECase e ps pos) =
  do (s1, t1, n1) <- ti env e
     (s2, t2, n2) <- let ((c, e):tl) = ps
                         th = (do
                                (env2, t2, n1) <- genPat env c
                                s3 <- unify ce t1 t2
                                (s4, t4, n2) <- ti (subSt (s1 `combineSubSt` s3) env2) e
                                return (s3 `combineSubSt` s4, subSt s4 t4, subSt s4 $ mergeNode n1 n2))
                     in foldl'
                          (\acc (c, e) ->
                             do
                               (s2, t2, n1) <- acc
                               (env3, t3, n2) <- genPat env c
                               s4 <- unify ce t1 t3
                               (s5, t5, n3) <- ti (subSt (s1 `combineSubSt` s2 `combineSubSt` s4) env3) e
                               s6 <- unify ce (subSt s5 t2) (subSt s5 t5)
                               return (s4 `combineSubSt` s5 `combineSubSt` s6, subSt s6 t5, subSt s6 $ mergeNode n1 $ mergeNode n2 n3)
                          )
                          th
                          tl
     let t = subSt s2 t2
      in do checkNestSignalType ce t
            return (s1 `combineSubSt` s2, t, subSt s2 $ NN ce t (mergeNode n1 n2))

typeInfer n = do
  r <- getInferred
  case Map.lookup n r of
    Nothing -> do
      s <- getSource
      case Map.lookup n s of
        Nothing -> throwError $ "cannot resolve the type of " ++ n
        Just e ->
          do
            --removeSource n
            setInferred n
            (s, t, _) <- ti nullTypeInferEnv e
            checkNestSignalType e t
            (TypeEnv ge) <- getGlobalEnv
            case Map.lookup n ge of
              Nothing ->
                do st <- generalize nullTypeInferEnv t
                   addGlobalEnv n st
                   return st
              Just (T.Scheme var tc) -> do
                s <- unify e t tc
                (let nt = subSt s t
                 in (if nt /= tc && n /= "main"
                     then typeMismatch e nt tc
                     else do
                            st <- generalize nullTypeInferEnv nt
                            addGlobalEnv n st
                            return st))
    Just True -> do
      t <- newTVar "a"
      st <- generalize nullTypeInferEnv t
      return st

runTI n env = (runStateT $ runErrorT $ typeInfer n) env
