module Resolver where

import qualified TypeInfer as TI
import qualified Type as T
import qualified AST as A
import qualified Module as M
import qualified Parser as P
import qualified Data.Map as Map
import Data.List
import Control.Monad.Error
import Control.Monad.State
import Text.Parsec.Pos (sourceName, sourceLine, sourceColumn)

type Modules = Map.Map String M.Module

nullModules = Map.empty

type Resolver a = ErrorT String (StateT Modules IO) a

importModule m n pre = do
	ms <- get
	case Map.lookup n ms of
		Nothing -> do
			r <- liftIO $ importFile n
			case r of
				Right nm -> do
					put $ Map.insert n nm ms
					importModule m n pre
				Left err -> throwError err
		Just nm -> do
		  m <- Map.foldlWithKey
		    (\acc k (v, pos) -> do
		        m <- acc
		        case M.addType k v pos m of
		        	Right m -> return m
		        	Left err -> throwError $ err ++ "\nwhen try to import " ++ n
		                                     ++ "\n    @ " ++ (show $ sourceName pos) ++ ":("
		                                     ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos) ++ ")\n"
		    )
		    (return m)
		    (M.types nm)
		  m <- Map.foldlWithKey
		    (\acc k v -> do
		        m <- acc
		        case M.addSource k v m of
		        	Right m -> return m
		        	Left err -> throwError $ err ++ "\nwhen try to import " ++ n
		                                     ++ "\n    @ " ++ (show $ sourceName (A.exprPos v)) ++ ":("
		                                     ++ (show $ sourceLine (A.exprPos v)) ++ ","
		                                     ++ (show $ sourceColumn (A.exprPos v)) ++ ")\n"
		    )
		    (return m)
		    (M.source nm)
		  m <- Map.foldlWithKey
		    (\acc k (v, pos) -> do
		        m <- acc
		        case M.addEnv k v pos m of
		        	Right m -> return m
		        	Left err -> throwError $ err ++ "\nwhen try to import " ++ n
		                                     ++ "\n    @ " ++ (show $ sourceName pos) ++ ":("
		                                     ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos) ++ ")\n"
		    )
		    (return m)
		    (M.env nm)
		  return m

importModules m =
	Map.foldlWithKey
	   (\acc n (pre, pos) -> do
	   	  m <- acc
	   	  importModule m n pre
	   )
	   (return m)
	   (M.imports m)

resolveModuleSource m =
  Map.foldlWithKey
   (\acc n e ->
    do
      m <- acc
      res <- liftIO $ TI.runResolve n $
             TI.typeState 0
                          (TI.TypeEnv $ Map.map (\(s, _)->s) $ M.env m)
                          (M.source m)
                          TI.nullResolved
      case res of
        (Right s, _) -> do
          return $ M.addEnv_ n s (A.exprPos e) m
        (Left err, _) -> do
          throwError err
  )
  (return m)
  (M.source m)

resolveType ts (T.TCon a b) pos = do
  resolveType ts a pos
  resolveTypeList ts b pos
resolveType ts (T.TCN a) pos =
  case Map.lookup a ts of
    Nothing -> throwError $ "type `" ++ a ++ "\' cannot be found"
                         ++ "\n    @ " ++ (show $ sourceName pos)
                         ++ ":(" ++ (show $ sourceLine pos)
                         ++ "," ++ (show $ sourceColumn pos)
                         ++ ")" ++ "\n"
    Just t -> return ()
resolveType ts (T.TFun a b) pos = do
  resolveTypeList ts a pos
  resolveType ts b pos
resolveType _ _ _ = return ()

resolveTypeList ts [] pos     = return ()
resolveTypeList ts (x:ps) pos = do
  resolveType ts x pos
  resolveTypeList ts ps pos

resolveModuleTypes m = do
  foldl'
    (\acc ((T.Scheme _ s), pos) -> do
       m <- acc
       resolveType (M.types m) s pos
       return m
    )
    (return m)
    (Map.elems (M.env m))


importFile file = do
  contents <- readFile $ file ++ ".hw"
  case P.iParse file contents of
    Left err -> return $ Left $ show err
    Right m -> do
      (r, _) <- runStateT (runErrorT (do
              m <- importModules $ M.addInitEnv m
              m <- resolveModuleTypes m
              resolveModuleSource m)) nullModules
      case r of
      	Right m -> return $ Right m
      	Left err -> return $ Left err

