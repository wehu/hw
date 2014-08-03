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

module Main where

import qualified Transformer as T
import qualified Resolver as R

import Control.Monad.Error
import Control.Monad.State

import System.Environment
import System.Console.GetOpt
import System.Process
import System.Exit

import Data.List
import qualified Data.Map as Map

data Flag = Help | I String | C String
        deriving Eq

options = [ Option ['h'] ["help"] (NoArg Help) "Show help information",
            Option ['i'] ["inc"] (ReqArg (\s -> I s) "PATH") "Specify search path",
            Option ['c'] ["clk"] (ReqArg (\s -> C s) "Clock") "Specify max clock"]

parseArgs argv = case getOpt Permute options argv of
        (opts, files, [])
                | (Help `elem` opts) || (files == []) -> ([], "0", [])
                | otherwise -> (map (\(I p) -> p) (filter (/=Help) opts),
                                (foldl' (\a o -> case o of (C c) -> c; _ -> a) "100" opts),
                                files)
        (_, _, errs) -> (errs, "0", [])

banner = "Usage: hw [-h] [-i PATH] [file ...]"

processFiles ps clk [] = return ()
processFiles ps clk (f:files) = do
        r <- R.importFile ps f Map.empty
        case r of
            Right m  -> do
                rr <- (runStateT $ runErrorT $ T.transform2hs clk m) T.nullSignalState
                case rr of
                    (Right res, _) -> do
                        writeFile (f ++ ".hs") res
                        let c = "runghc " ++ f ++ ".hs"
                         in do ec <- system c
                               es <- exitSuccess
                               if ec == es
                               then return ()
                               else putStrLn $ "run command `" ++ c ++ "\' failed"
                    (Left err, _) -> putStrLn err
            Left err -> putStrLn err
        processFiles ps clk files

main = do
    argv <- getArgs
    case parseArgs argv of
        (ms, _, []) -> putStrLn $ unlines ms ++ usageInfo banner options
        (ps, c, files) -> processFiles ps c files
