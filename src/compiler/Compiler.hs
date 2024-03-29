module Compiler
    ( compile
    )
where

import           AbsLatte
import           CCommon
import           CStmts
import           CClasses

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Map                      as M
                                                ( Map
                                                , empty
                                                , elems
                                                , fromList
                                                )

compile (Program prog) = evalStateT
    (runReaderT (go prog) (CEnv 0 M.empty Nothing))
    (CState 0 0 "" M.empty predefinedFns M.empty M.empty)
  where
    go prog = do
        saveClassesMembers prog
        vmtsCode <- createVMTs
        flip ($) [] <$> translate vmtsCode prog >>= printInstrs
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
        let args' = M.fromList $ zipWith
                (\(Arg t (Ident var)) i -> (var, (Param i, t)))
                args
                [1 ..]
        (_, code) <- local (\env -> env { varMem = args' })
                           (transStmt (BStmt b))
        state <- get
        return
            $ instrSS
                  [Lab $ FuncLabel name, Prologue, StackAlloc $ locals state]
            . code
            . instrSS [Lab $ FuncLabel $ retLabel state, Epilogue, ZIns RET]
    ClDef (Ident clsName) _ clmembers -> do
        x <- mapM (transMethods clsName) clmembers
        return $ foldr (.) id x
