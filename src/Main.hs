module Main where

import Resolver as R

import System.Environment
import System.Console.GetOpt
import Data.List

data Flag = Help | P String
        deriving Eq

options = [ Option ['h'] ["help"] (NoArg Help) "Show help information",
            Option ['i'] ["inc"] (ReqArg (\s -> P s) "PATH") "Specify search path"]

parseArgs argv = case getOpt Permute options argv of
        (opts, files, [])
                | (Help `elem` opts) || (files == []) -> ([], [])
                | otherwise -> (map (\(P p) -> p) (filter (/=Help) opts), files)
        (_, _, errs) -> (errs, [])

banner = "Usage: test.hs [-h] [-i PATH] [file ...]"

processFiles ps [] = return ()
processFiles ps (f:files) = do
        r <- R.importFile ps f
        case r of
        	Right m  -> putStrLn $ show m
        	Left err -> putStrLn err
        processFiles ps files

main = do
    argv <- getArgs
    case parseArgs argv of
        (ms, []) -> putStrLn $ unlines ms ++ usageInfo banner options
        (ps, files) -> processFiles ps files
