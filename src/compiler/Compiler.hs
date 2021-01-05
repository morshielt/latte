module Compiler
    ( compile
    , x86
    )
where

import           AbsLatte
import           PrintLatte
-- import           SACommon                       ( TCType )
import           CCommon
-- import           CExprs
import           CStmts
import           CClasses

import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Trans.Except
import           Data.Bits                      ( (.&.) )
import           Data.List                      ( nubBy
                                                , intercalate
                                                )
import           Data.Map                      as M
                                                ( Map
                                                , empty
                                                , lookup
                                                , insert
                                                , size
                                                , elems
                                                , fromList
                                                , toList
                                                , union
                                                )
--DONE: wywołanie error() liczy się jako return w return checkerze!!!
--DONE: spr w typecheck czy ktoś nie deklaruje klasy 'bool' 'int' czy coś XDDD nie da się
--DONE: zmienne o nazwie self w metodach!
--DONE: porównanie stringów to porównanie referencji czy zawartości?
--DONE:[ale jakoś szału nie ma xD] poprawić transCond domyślny na ręcznie napisany
--DONE: co jak nazwiemy zmienną 'null'? nic, whatever, czemu nie XD
-- DONE: czy (A)null == (B)null? nie powinno, typecheck poiwnien wywalać
--DONE: przetestować tablice tablic/obiektów/stringów
--DONE: strcmp stringów pełen
--DONE: list.s, VTable niech się nie ładuje/wypisuje
--TODO: skrypt na studentsa
--TODO: refactor
--TODO: podzielić na pliki
--TODO: README o studentsie i jakie rozszerzenia są
--TODO: importy ogar


x86 :: [Instr] -> CM String
x86 ins = return $ (unlines . map (\x -> indent x ++ show x)) ins

compile (Program prog) = evalStateT
    (runReaderT (go prog) (CEnv 0 M.empty))
    (CState 0 0 0 0 0 "" M.empty predefinedFns M.empty M.empty Nothing Nothing)
  where
    go prog = do
        saveClassesMembers prog
        vmtsCode <- createVMTs
        flip ($) [] <$> translate vmtsCode prog >>= x86
    predefinedFns :: M.Map Var Type
    predefinedFns = M.fromList
        [ ("printInt"           , Void)
        , ("printString"        , Void)
        , ("error"              , Void)
        , ("readInt"            , Int)
        , ("readString"         , Str)
        , ("concatStrings_____" , Str)
        , ("compareStrings_____", Bool)
        ]


translate :: InstrS -> [TopDef] -> CM InstrS
translate vmtsCode tds = do
    code <- foldM go id tds
    strs <- gets strings
    let strLabels = map Lab $ M.elems strs
    return
        $ instrSS [Intro, DataSection]
        . instrSS strLabels
        . vmtsCode
        . instrS TextSection
        . code
  where
    go accCode stmt = do
        code <- transTopDef stmt
        return (accCode . code)

transTopDef :: TopDef -> CM InstrS
transTopDef x = case x of
    FnDef ret (Ident name) args b -> do
        modify (\st -> st { locals = 0, retLabel = "ret_" ++ name })
        (_, code) <- local
            (\env -> env
                { varMem = M.fromList $ zipWith
                               (\(Arg t (Ident var)) i -> (var, (Param i, t)))
                               args
                               [1 ..]
                }
            )
            (transStmt (BStmt b))
        -- vars   <- countVars ss
        state <- get
        return
            $ instrSS
                  [Lab $ FuncLabel name, Prologue, StackAlloc $ locals state]
            . code
            . instrSS [Lab $ FuncLabel $ retLabel state, Epilogue, ZIns RET]
    ClDef (Ident clsName) _ clmembers -> do
        x <- mapM (transMethods clsName) clmembers
        return $ foldr (.) id x

-- DONE: stack align 16 jeśli trzeba [NIE TRZEBA]
