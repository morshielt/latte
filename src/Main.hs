import           ParLatte
import           AbsLatte
import           ErrM

import           StaticAnalysis                 ( runStaticAnalysis )
import           Compiler                       ( compile )

import           Control.Monad.Except           ( runExceptT )
import           System.Environment             ( getArgs )
import           System.Exit                    ( exitFailure )
import           System.IO                      ( stderr
                                                , hPutStrLn
                                                , hPutStr
                                                )
import           System.FilePath.Posix          ( replaceExtension
                                                , takeBaseName
                                                )

check :: String -> IO String
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
            Right _ -> do
                genCode <- runExceptT $ compile tree
                case genCode of
                    Left e -> do
                        hPutStrLn stderr $ "[Compilation error] " ++ e
                        exitFailure
                    Right strs -> do
                        hPutStr stderr "OK\n" -- TODO: czy to 'OK' nadal ma się wypisywać? i czy kompilować też sam typecheck do latc?
                        return strs

saveFile :: String -> String -> IO ()
saveFile filename content = do
    let extension = ".s"
    let name = replaceExtension filename extension
    writeFile name content

main :: IO ()
main = do
    args <- getArgs
    case args of
        [file] -> readFile file >>= check >>= saveFile file
        _      -> do
            putStrLn "usage: ./latc_x86 <src_file>"
            exitFailure
