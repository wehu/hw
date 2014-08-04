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

module Resolver(
  initResolverEnv,
  importFile
) where

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
import System.Directory
import Control.Exception
import System.Exit

type Modules = Map.Map String M.Module

nullModules = Map.empty

type Resolver a = ErrorT String (StateT Modules IO) a

importModule ps m n pre fs pos poses = do
  ms <- get
  case Map.lookup n ms of
    Nothing -> do
                 r <- liftIO $ importFile_ ps n fs pos poses
                 case r of
                   Right nm -> do
                     put $ Map.insert n nm ms
                     importModule ps m n pre fs pos poses
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

importModules ps m fs poses =
  Map.foldlWithKey
     (\acc n (pre, pos) -> do
         m <- acc
         importModule ps m n pre fs pos poses
     )
     (return m)
     (M.imports m)

initResolverEnv m = TI.typeInferState 0
                          (TI.TypeEnv $ Map.map (\(s, _)->s) $ M.env m)
                          (M.source m)
                          TI.nullInferred

resolveModuleSource m =
  Map.foldlWithKey
   (\acc n e ->
    do
      m <- acc
      res <- liftIO $ TI.runTI n $ initResolverEnv m
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
                         ++ ")\n"
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
  foldM
    (\m ((T.Scheme _ s), pos) -> do
       resolveType (M.types m) s pos
       return m
    )
    m
    (Map.elems (M.env m))


importFile_ ps file fs pos poses = do
  fn <- foldM
          (\acc p ->
            foldM
              (\a f -> do
                if a == ""
                then do e <- doesFileExist f
                        if e then return f else return a
                else return a
              )
              acc
              [file, file ++ ".hw", p ++ "/" ++ file, p ++ "/" ++ file ++ ".hw"]
          )
          ""
          ps
  contents <- catch (readFile (if fn == "" then file else fn))
                    (\e ->
                       let err = show (e :: IOException) ++ "\n" ++
                                  "import " ++ file ++ " failed\n" ++
                                  foldl' (\acc (f, pos) -> acc ++ "  from " 
                                          ++ f ++ ":(" ++ (show $ sourceLine pos)
                                          ++ "," ++ (show $ sourceColumn pos) ++")\n")
                                         ""
                                         (zip fs poses)
                       in do putStrLn err
                             exitFailure)
  case P.iParse fn contents of
    Left err -> return $ Left $ show err
    Right m -> do
      (r, _) <- runStateT (runErrorT (
              if elem fn fs
              then throwError $ "circle importing `" ++ file ++ "\'\n" ++
                                foldl' (\acc (f, pos) -> acc ++ "  from " 
                                        ++ f ++ ":(" ++ (show $ sourceLine pos)
                                        ++ "," ++ (show $ sourceColumn pos) ++")\n")
                                       ""
                                       (zip fs poses)
              else do
                     m <- importModules ps (M.addInitEnv m) (fn:fs) (pos:poses)
                     m <- resolveModuleTypes m
                     resolveModuleSource m)) nullModules
      case r of
        Right m -> return $ Right m
        Left err -> return $ Left err

importFile ps file = importFile_ ps file [] M.sysSourcePos []