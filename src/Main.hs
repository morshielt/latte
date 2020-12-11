import           System.Environment             ( getArgs )
import           System.Exit                    ( exitFailure )
import           System.IO                      ( stderr
                                                , hPutStrLn
                                                )
import           Control.Monad.Except

import           ParLatte
import           AbsLatte

import           StaticAnalysis                 ( runStaticAnalysis )
-- import           Interpreter

import           ErrM

import           Control.Monad                  ( when )
import           PrintLatte

check :: String -> IO ()
check s = case pProgram (myLexer s) of
    Bad err -> do
        hPutStrLn stderr $ "[Syntax error] " ++ err
        exitFailure
    Ok tree -> do
        tcRes <- runExceptT $ runStaticAnalysis tree
        case tcRes of
            Left e -> do
                hPutStrLn stderr $ "[Typecheck exception]\n" ++ e
                exitFailure
            Right _ -> return ()

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
    putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
    putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
    args <- getArgs
    case args of
        [file] -> readFile file >>= check
        []     -> getContents >>= check
        _      -> do
            putStrLn "usage: ./latc <src_file>"
            exitFailure
