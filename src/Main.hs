import           ParLatte
import           AbsLatte
import           ErrM

import           StaticAnalysis                 ( runStaticAnalysis )

import           Control.Monad.Except           ( runExceptT )
import           System.Environment             ( getArgs )
import           System.Exit                    ( exitFailure )
import           System.IO                      ( stderr
                                                , hPutStrLn
                                                , hPutStr
                                                )

check :: String -> IO ()
check s = case pProgram (myLexer s) of
    Bad err -> do
        hPutStrLn stderr $ "ERROR\n[Syntax error]\n " ++ err
        exitFailure
    Ok tree -> do
        tcRes <- runExceptT $ runStaticAnalysis tree
        case tcRes of
            Left e -> do
                hPutStr stderr $ "ERROR\n[Typecheck exception]\n" ++ e
                exitFailure
            Right _ -> hPutStr stderr "OK\n"

main :: IO ()
main = do
    args <- getArgs
    case args of
        [file] -> readFile file >>= check
        []     -> getContents >>= check
        _      -> do
            putStrLn "usage: ./latc <src_file>"
            exitFailure
