module SAStmts
    ( checkStmtM
    )
where

import           AbsLatte
import           PrintLatte                     ( printTree )

import           SACommon
import           SAExprs

import           Control.Monad.Reader
import           Data.Map                      as M
                                                ( insert )

checkStmtM :: Stmt -> TCM TCEnv
checkStmtM Empty    = ask

checkStmtM (SExp e) = do
    _ <- checkExpr e
    ask

checkStmtM (Decl t ds) = do
    when (checkIfVoid t) $ throwTCM "Illegal void type variable declaration"
    checkIfClassExistsT t
    env <- ask
    foldM go env ds
  where
    go :: TCEnv -> Item -> TCM TCEnv
    go acc d = do
        t' <- typeToTCType t
        local (const acc) $ handleDecl t' d

    handleDecl :: TCType -> Item -> TCM TCEnv
    handleDecl t d = do
        var <- case d of
            (NoInit (Ident var)) -> return var
            (Init (Ident var) e) -> matchExpType t e >> return var

        checkIfNameAlreadyInScope var
        env <- ask
        let envWithDecl = M.insert var (t, scope env) (types env)
        return $ env { types = envWithDecl }

checkStmtM (BStmt (Block ss)) = do
    env <- ask
    s   <- asks scope
    local (\env -> env { scope = s + 1 }) (checkStmtsM ss)
    ask
  where
    checkStmtsM :: [Stmt] -> TCM TCEnv
    checkStmtsM ss = do
        env <- ask
        foldM go env ss
      where
        go :: TCEnv -> Stmt -> TCM TCEnv
        go env' s = local (const env') $ checkStmtM s `throwExtraMsg` msg
            where msg e = e ++ " in statement:\n" ++ printTree s

checkStmtM (Ass assignable e) = do
    t <- checkExpr assignable
    matchExpType t e
    ask

checkStmtM (Incr e                         ) = checkIncrDecr e
checkStmtM (Decr e                         ) = checkIncrDecr e

checkStmtM (While e s                      ) = checkWhileIf e [s]
checkStmtM (Cond  e s                      ) = checkWhileIf e [s]
checkStmtM (CondElse e s1 s2               ) = checkWhileIf e [s1, s2]

checkStmtM (For type_ (Ident iter) arr stmt) = do
    checkIfClassExistsT type_
    (TArr t) <- matchExpType wildcardArr arr
    t'       <- typeToTCType type_
    matchType [t'] t
    env <- ask
    let typesWithIter = M.insert iter (t, scope env + 1) (types env)
    let stmt' = case stmt of
            (BStmt _) -> stmt
            _         -> BStmt (Block [stmt])
    local (\env -> env { types = typesWithIter }) (checkStmtM stmt')
    ask

checkStmtM VRet    = matchReturn TVoid
checkStmtM (Ret e) = matchReturn =<< checkExpr e

matchReturn t = do
    ex <- asks expectedRet
    case ex of
        Nothing -> throwTCM "Return outside of function"
        Just eT -> matchType [eT] t `throwExtraMsg` msg
    ask
    where msg e = "Invalid return type\n" ++ e

checkWhileIf :: Expr -> [Stmt] -> TCM TCEnv
checkWhileIf e [s] = matchExpType TBool e >> checkAsBStmt s >> ask
checkWhileIf e [s1, s2] =
    matchExpType TBool e >> checkAsBStmt s1 >> checkAsBStmt s2 >> ask
checkWhileIf _ _ =
    throwTCM "Impossible - while/if has 1 or 2 statements to check."

checkAsBStmt :: Stmt -> TCM TCEnv
checkAsBStmt s@(BStmt _) = checkStmtM s
checkAsBStmt s           = checkStmtM (BStmt (Block [s]))

checkIncrDecr :: Expr -> TCM TCEnv
checkIncrDecr e = checkExpr e >>= matchType [TInt] >> ask
