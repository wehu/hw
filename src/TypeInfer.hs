{-# LANGUAGE FlexibleInstances #-}

module TypeInfer(
  Types(..),
  TypeEnv(..),
  typeState,
  nullResolved,
  runResolve
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

nullEnv = TypeEnv Map.empty

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

type Resolved = Map.Map String Bool

nullResolved = Map.empty

data TypeState = TypeState {varc :: Int, globalEnv :: TypeEnv, source :: M.Source, resolved :: Resolved}

typeState c e s r = TypeState {varc = c, globalEnv = e, source = s, resolved = r}
initTypeState = typeState 0 nullEnv Map.empty Map.empty

type TI a = ErrorT String (StateT TypeState IO) a

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

getResolved :: TI (Resolved)
getResolved = do
  s <- get
  return $ resolved s

setResolved :: String -> TI ()
setResolved n = do
  s <- get
  put s{resolved = Map.insert n True (resolved s)}

instantiate (T.Scheme vars t) = do
  nvars <- mapM (\_-> newTVar "a") vars
  let s = Map.fromList (zip vars nvars)
    in return $ subSt s t

typeMismatch e t1 t2 = throwError $
                         "Error : type `" ++ (show t1) ++ "\' mismatch with type `" ++ (show t2)
                         ++ "\'\n    @ " ++ (show $ sourceName $ A.exprPos e)
                         ++ ":(" ++ (show $ sourceLine $ A.exprPos e)
                         ++ "," ++ (show $ sourceColumn $ A.exprPos e)
                         ++ ")" ++ "\n\n" ++ (show e) ++ "\n"

unify :: A.Exp -> T.Type -> T.Type -> TI SubSt
unify e (T.TFun l r) (T.TFun l' r') = do
  if length l /= length l'
  then typeMismatch e l l'
  else do s1 <- foldl'
                  (\acc (a, a') ->
                     do s <- acc
                        s' <- unify e (subSt s a) (subSt s a')
                        return $ s `combineSubSt` s')
                  (return nullSubSt)
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
                     ++ ")" ++ "\n\n" ++ (show e) ++ "\n"
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
         (s'', t) <- ti (subSt s' (TypeEnv env')) pat
         return (TypeEnv env', subSt s'' t)

ti :: TypeEnv -> A.Exp -> TI (SubSt, T.Type)
ti (TypeEnv env) e@(A.EVar a _) = do
  case Map.lookup a env of
    Nothing ->
      do (TypeEnv ge) <- getGlobalEnv
         case Map.lookup a ge of
           Nothing -> do
             (T.Scheme _ t) <- resolve a
             checkNestSignalType e t
             return (nullSubSt, t)
           Just s -> do
             t <- instantiate s
             checkNestSignalType e t
             return (nullSubSt, t)
    Just s  -> do
      t <- instantiate s
      checkNestSignalType e t
      return (nullSubSt, t)
ti _ (A.ELit (A.LInt _) _) = return (nullSubSt, T.TInt)
ti _ (A.ELit (A.LBool _) _) = return (nullSubSt, T.TBool)
ti _ (A.ELit (A.LStr _) _) = return (nullSubSt, T.TStr)
ti _ (A.ELit (A.LFloat _) _) = return (nullSubSt, T.TFloat)
ti _ (A.ELit (A.LDouble _) _) = return (nullSubSt, T.TDouble)
ti env e@(A.ECon (A.CCon "[]" []) _) = do
  t <- newTVar "a"
  let nt = T.TCon (T.TCN "[]") [t]
   in (do
        checkNestSignalType e nt
        return (nullSubSt, nt))
ti env e@(A.ECon (A.CCon "[]" (h:ps)) _) = do
  (s, t) <- foldl'
              (\acc p ->
                 do (s1, t1) <- acc
                    (s2, t2) <- ti (subSt s1 env) p
                    s3 <- unify e (subSt s2 t1) (subSt s2 t2)
                    return (s1 `combineSubSt` s2 `combineSubSt` s3, subSt s3 t2)
              )
              (ti env h)
              ps
  let nt = T.TCon (T.TCN "[]") [t]
   in do
        checkNestSignalType e nt
        return (s, nt)
ti env e@(A.ECon (A.CCon c []) pos) =
  if c == "()"
  then
    let t = T.TCon (T.TCN "()") []
     in do checkNestSignalType e t
           return $ (nullSubSt, t)
  else ti env (A.EVar c pos)
ti env e@(A.ECon (A.CCon c ps) pos) =
  if c == "()"
  then do
    (s, ts) <- foldl'
      (\acc e-> do
        (s, ot) <- acc
        (s1, t) <- ti (subSt s env) e
        return (s1, ot ++ [t])
      )
      (return (nullSubSt, []))
      ps
    let t = subSt s $ T.TCon (T.TCN "()") ts
     in do
         checkNestSignalType e t
         return $ (s, t)
  else ti env (A.EApp (A.EVar c pos) ps pos)
ti env e@(A.EApp a [] _) =
  do nt <- newTVar "a"
     (s, t) <- ti env a
     s' <- unify e t (T.TFun [] nt)
     let nt' = subSt s' nt
      in do checkNestSignalType e nt'
            return (s `combineSubSt` s', nt')
ti env e@(A.EApp a ps _) =
  do nt <- newTVar "a"
     (sa, ta) <- ti env a
     (sp, tp) <- let (h:tl) = ps
                     th = (ti (subSt sa env) h) >>= (\(s, t) -> return (s, [t]))
                 in foldl'
                      (\acc e ->
                         do (s1, ts) <- acc
                            (s2, t) <- ti (subSt s1 env) e
                            return (s1 `combineSubSt` s2, ts ++ [t]))
                      th
                      tl
     s <- unify e ta (T.translateFunType $ T.TFun tp nt)
     let nt' = subSt s nt
      in do checkNestSignalType e nt'
            return (s `combineSubSt` sp `combineSubSt` sa, nt')
ti env ae@(A.EAbs cs e pos) =
  do (env1, ts) <- let (h:tl) = cs
                       th = (do
                               (env', t) <- genPat env h
                               return (env', [t]))
                 in foldl'
                      (\acc e ->
                         do (TypeEnv env1, ts) <- acc
                            (TypeEnv env2, t) <- genPat (TypeEnv env1) e
                            return (TypeEnv $ env2 `Map.union` env1, ts ++ [t]))
                      th
                      tl
     (s, t) <- ti env1 e
     let nt = subSt s $ T.translateFunType $ T.TFun ts t
      in do checkNestSignalType ae nt
            return (s, nt)
ti env fe@(A.EFun n [] e pos) =
  do (s, t) <- ti env e
     (let ft = subSt s t
      in (do ns <- generalize (remove env n) ft
             --addGlobalEnv n ns
             checkNestSignalType fe ft
             return (s, ft)))
ti env fe@(A.EFun n cs e pos) =
  do (env1, ts) <- let (h:tl) = cs
                       th = (do
                               (env', t) <- genPat env h
                               return (env', [t]))
                 in foldl'
                      (\acc e ->
                         do (TypeEnv env1, ts) <- acc
                            (TypeEnv env2, t) <- genPat (TypeEnv env1) e
                            return (TypeEnv $ env2 `Map.union` env1, ts ++ [t]))
                      th
                      tl
     (s, t) <- ti env1 e
     (let ft = subSt s $ T.translateFunType $ T.TFun ts t
      in (do ns <- generalize (remove env n) ft
             --addGlobalEnv n ns
             checkNestSignalType fe ft
             return (s, ft)))
ti env le@(A.ELet ps e pos) = 
  do (env1, s1, t1) <- let ((c, e):tl) = ps
                           th = (do
                                  (env1, t1) <- genPat env c
                                  (s2, t2) <- ti env e
                                  s3 <- unify le (subSt s2 t1) (subSt s2 t2)
                                  env2 <- generalizeL (subSt s3 env1) (Set.toList (ftvPat c))
                                  return (env2, s2 `combineSubSt` s3, subSt s3 t2))
                       in foldl'
                            (\acc (c, e) ->
                               do (TypeEnv env1, s1, t1) <- acc
                                  (TypeEnv env2, t2) <- genPat (TypeEnv env1) c
                                  (s3, t3) <- ti (subSt s1 (TypeEnv env1)) e
                                  s4 <- unify le (subSt s3 t2) (subSt s3 t3)
                                  env3 <- generalizeL (subSt s4 (TypeEnv env2)) (Set.toList (ftvPat c))
                                  return (TypeEnv $ env2 `Map.union` env1,  s1 `combineSubSt` s3 `combineSubSt` s4, subSt s4 t3)
                            )
                            th
                            tl
     (s2, t2) <- ti (subSt s1 env1) e
     let t = subSt s2 t2
      in do checkNestSignalType le t
            return (s1 `combineSubSt` s2, t)
ti env e@(A.EIf c e1 e2 pos) =
  do (s1, t1) <- ti env c
     if t1 /= T.TBool
     then typeMismatch e t1 T.TBool
     else do
            (s2, t2) <- ti (subSt s1 env) e1
            (s3, t3) <- ti (subSt s1 env) e2
            s4 <- unify e (subSt s1 t2) (subSt s1 t3)
            let t = subSt s4 t2
             in do checkNestSignalType e t
                   return (s1 `combineSubSt` s2 `combineSubSt` s3 `combineSubSt` s4, t)
ti env ce@(A.ECase e ps pos) =
  do (s1, t1) <- ti env e
     (s2, t2) <- let ((c, e):tl) = ps
                     th = (do
                            (env2, t2) <- genPat env c
                            s3 <- unify ce t1 t2
                            (s4, t4) <- ti (subSt (s1 `combineSubSt` s3) env2) e
                            return (s3 `combineSubSt` s4, subSt s4 t4))
                 in foldl'
                      (\acc (c, e) ->
                         do
                           (s2, t2) <- acc
                           (env3, t3) <- genPat env c
                           s4 <- unify ce t1 t3
                           (s5, t5) <- ti (subSt (s1 `combineSubSt` s2 `combineSubSt` s4) env3) e
                           s6 <- unify ce (subSt s5 t2) (subSt s5 t5)
                           return (s4 `combineSubSt` s5 `combineSubSt` s6, subSt s6 t5)
                      )
                      th
                      tl
     let t = subSt s2 t2
      in do checkNestSignalType ce t
            return (s1 `combineSubSt` s2, t)

resolve n = do
  r <- getResolved
  case Map.lookup n r of
    Nothing -> do
      s <- getSource
      case Map.lookup n s of
        Nothing -> throwError $ "cannot resolve the type of " ++ n
        Just e ->
          do
            --removeSource n
            setResolved n
            (s, t) <- ti nullEnv e
            checkNestSignalType e t
            (TypeEnv ge) <- getGlobalEnv
            case Map.lookup n ge of
              Nothing ->
                do st <- generalize nullEnv t
                   addGlobalEnv n st
                   return st
              Just (T.Scheme var tc) -> do
                s <- unify e t tc
                (let nt = subSt s t
                 in (if False
                     then typeMismatch e nt tc
                     else do
                            st <- generalize nullEnv nt
                            addGlobalEnv n st
                            return st))
    Just True -> do
      t <- newTVar "a"
      st <- generalize nullEnv t
      return st

--runTi env e s = (runStateT $ runErrorT $ ti env e) s
runResolve n env = (runStateT $ runErrorT $ resolve n) env