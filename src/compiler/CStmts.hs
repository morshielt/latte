module CStmts
    ( transStmt
    )
where

import           AbsLatte
import           CCommon
import           CExprs

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Map                      as M
                                                ( insert )

-- statements --------------------------------------------
transStmt :: Stmt -> CM (CEnv, InstrS)
transStmt Empty = do
    env <- ask
    return (env, id)
transStmt VRet = do
    env <- ask
    lab <- gets retLabel
    return (env, instrS $ Jump JMP $ FuncLabel lab)
transStmt (Ret e) = do
    code <- transExpr e
    env  <- ask
    lab  <- gets retLabel
    return (env, code . instrSS [Jump JMP $ FuncLabel lab])
transStmt (SExp e) = do
    code <- transExpr e
    env  <- ask
    return (env, code)
transStmt (Cond e s) = do
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel

    condCode   <- transCond e trueLabel afterLabel
    trueCode   <- transAsBStmt s
    let op = instrS (Lab $ JmpLabel trueLabel) . trueCode . instrS
            (Lab $ JmpLabel afterLabel)
    env <- ask
    return (env, condCode . op)
transStmt (CondElse e s1 s2) = do
    trueLabel  <- getFreeLabel
    falseLabel <- getFreeLabel
    afterLabel <- getFreeLabel

    condCode   <- transCond e trueLabel falseLabel
    trueCode   <- transAsBStmt s1
    falseCode  <- transAsBStmt s2
    let op =
            instrS (Lab $ JmpLabel trueLabel)
                . trueCode
                . instrS (Jump JMP $ JmpLabel afterLabel)
                . instrS (Lab $ JmpLabel falseLabel)
                . falseCode
                . instrS (Lab $ JmpLabel afterLabel)
    env <- ask
    return (env, condCode . op)
transStmt (While e s) = do
    afterLabel <- getFreeLabel
    condLabel  <- getFreeLabel
    loopLabel  <- getFreeLabel

    condCode   <- transCond e loopLabel afterLabel
    loopCode   <- transAsBStmt s
    env        <- ask
    return
        ( env
        , instrS (Jump JMP $ JmpLabel condLabel)
        . instrS (Lab $ JmpLabel loopLabel)
        . loopCode
        . instrS (Lab $ JmpLabel condLabel)
        . condCode
        . instrS (Lab $ JmpLabel afterLabel)
        )
transStmt (Decl t ds) = do
    env <- ask
    foldM (goDecl t) (env, id) ds
  where
    goDecl :: Type -> (CEnv, InstrS) -> Item -> CM (CEnv, InstrS)
    goDecl t (env', accCode) d = do
        (env'', code) <- local (const env') $ handleDecl t d
        return (env'', accCode . code)
      where
        handleDecl :: Type -> Item -> CM (CEnv, InstrS)
        handleDecl t d = do
            state <- get
            sco   <- asks scope
            let loc = Local $ locals state + 1
            modify (\st -> st { locals = locals state + 1 })
            (var, code) <- case d of
                (NoInit (Ident var)) -> do
                    def <- defaultValue t
                    return (var, instrS $ MOV def (Mem loc))
                (Init (Ident var) e) -> do
                    initCode <- transExpr e
                    return (var, initCode . instrSS [MOV (Reg EAX) (Mem loc)])
            env <- ask
            let envWithDecl = M.insert var (loc, t) $ varMem env
            return (env { varMem = envWithDecl }, code)
          where
            defaultValue :: Type -> CM Operand
            defaultValue Int  = return $ Lit 0
            defaultValue Bool = return falseLit
            defaultValue _    = return nullPtr

transStmt (Ass ass e) = do
    accCode  <- transLValue ass
    exprCode <- transExpr e
    env      <- ask
    return
        ( env
        , accCode . instrS (PUSH $ Reg EAX) . exprCode . instrSS
            [POP $ Reg EDX, MOV (Reg EAX) $ Addr 0 EDX]
        )
transStmt (Incr ass) = do
    accCode <- transLValue ass
    env     <- ask
    return (env, accCode . instrSS [UnIns INC $ Addr 0 EAX])
transStmt (Decr ass) = do
    accCode <- transLValue ass
    env     <- ask
    return (env, accCode . instrSS [UnIns DEC $ Addr 0 EAX])
transStmt (BStmt (Block ss)) = do
    env <- ask
    local (\env -> env { scope = scope env + 1 }) $ transStmts ss
  where
    transStmts :: [Stmt] -> CM (CEnv, InstrS)
    transStmts ss = do
        env       <- ask
        (_, code) <- foldM go (env, id) ss
        return (env, code)
      where
        go :: (CEnv, InstrS) -> Stmt -> CM (CEnv, InstrS)
        go (env', accCode) s = do
            (env'', code) <- local (const env') $ transStmt s
            return (env'', accCode . code)
transStmt (For t ident arr stmt) =
    let iter    = Ident "___iter"
        arr_ptr = Ident "___arr_ptr"
        toWhile type_ = BStmt $ Block
            [ Decl Int   [NoInit iter]
            , Decl type_ [Init arr_ptr arr]
            , While
                (ERel (EVar iter) LTH (EAttrAcc (EVar arr_ptr) (Ident "length"))
                )
                (BStmt $ Block
                    [ Decl t [Init ident (EArrAcc (EVar arr_ptr) (EVar iter))]
                    , stmt
                    , Incr (EVar iter)
                    ]
                )
            ]
    in  do
            type_ <- getExprType arr
            transStmt $ toWhile type_

transAsBStmt :: Stmt -> CM InstrS
transAsBStmt s@(BStmt _) = do
    (_, code) <- transStmt s
    return code
transAsBStmt s = do
    (_, code) <- transStmt (BStmt (Block [s]))
    return code
