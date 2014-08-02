module Main where

import qualified Transformer as T
import qualified Resolver as R

import Control.Monad.Error
import Control.Monad.State

import System.Environment
import System.Console.GetOpt
import System.Process
import System.Exit

data Flag = Help | I String
        deriving Eq

options = [ Option ['h'] ["help"] (NoArg Help) "Show help information",
            Option ['i'] ["inc"] (ReqArg (\s -> I s) "PATH") "Specify search path"]

parseArgs argv = case getOpt Permute options argv of
        (opts, files, [])
                | (Help `elem` opts) || (files == []) -> ([], [])
                | otherwise -> (map (\(I p) -> p) (filter (/=Help) opts), files)
        (_, _, errs) -> (errs, [])

banner = "Usage: hw [-h] [-i PATH] [file ...]"

processFiles ps [] = return ()
processFiles ps (f:files) = do
        r <- R.importFile ps f
        case r of
            Right m  -> do
                rr <- (runStateT $ runErrorT $ T.transform2hs m) T.nullSignalState
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
        processFiles ps files

main = do
    argv <- getArgs
    case parseArgs argv of
        (ms, []) -> putStrLn $ unlines ms ++ usageInfo banner options
        (ps, files) -> processFiles ps files
