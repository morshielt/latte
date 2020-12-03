module StaticAnalysis
    ( runStaticAnalysis
    )
where


import           AbsLatte

import           SATypes
import           SAUtils
import           PrintLatte

import           Control.Monad.Reader
import           Control.Monad.Trans.Except

import           Data.List                      ( intercalate )
import           Data.Map                       ( Map
                                                , union
                                                , insert
                                                , fromList
                                                , empty
                                                )

import           Control.Monad                  ( when )

-- TODO: to chyba też już nie w typechecku
-- int[][] arr = new int[][20];
-- arr[1] = 5; -- TODO: co tu w ogóle można przypisać? tablicę odp. długości czy nic czy co????

-- TODO: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?

-- TODO:
-- Są dostępne predefiniowane funkcje:
-- void printInt(int)
-- void printString(string)
-- void error()
-- int readInt()
-- string readString()

-- TODO: check if main present
-- TODO: cykliczne `extends`
-- TODO: do BStmt chyba potrzebuję jednak Reader monad?

runStaticAnalysis (Program prog) = runReaderT (checkTopDefsM prog)
    $ TCEnv empty empty 0 Nothing
  where
    initialTypes :: Map Var (TCType, Scope)
    initialTypes = empty

    -- go prog = do

    --     checkTopDefsM prog
        -- checkReturns prog
        -- get

-- TODO: ^może nawet tu wyżej w runStaticAnalysis taki init mapy dać!!!
-- TODO: ^jedno przejście po topdefach dodać tylko że dane funkcje/klasy istnieją, żeby potem w środku było, że są!!!
checkTopDefsM :: [TopDef] -> TCM TCEnv
checkTopDefsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ checkTopDefM s

-- checkTopDefsM :: [TopDef] -> TCM ()
-- checkTopDefsM []       = return ()
-- checkTopDefsM (s : ss) = do
--     checkTopDefM s
--     checkTopDefsM ss
--   where
--     go :: TCEnv -> TopDef -> TCM TCEnv
--     go env' s = local (const env') $ checkTopDefM s

checkTopDefM :: TopDef -> TCM TCEnv
checkTopDefM (FnDef ret (Ident name) args (Block stmts)) = do
    checkIfNameAlreadyInScope name
    checkStmtsM stmts
    -- let ret' = typeToTCType ret
    -- scope <- gets scope
    -- env   <- get

    -- let t    = TFun (map argToTCArg args) ret'
    -- let fEnv = env { types = insert name (t, scope) (types env) }

    -- argsTypes <- handleArgs args `throwExtraMsg` msg
    -- let fEnvWithArgs = fEnv { types       = argsTypes `union` types fEnv
    --                         , expectedRet = Just (ret', name)
    --                         }
    -- return ()

--     ask

checkTopDefM (ClDef (Ident ident) classext clmembers) = undefined

--- STMTS -----------------------------------------------------------------

checkStmtsM :: [Stmt] -> TCM TCEnv
checkStmtsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> Stmt -> TCM TCEnv
    -- TODO: czy to `throwExtraMsg` nie działa źle z BStmt? whelp, działa śmiesznie
    -- mogę ew rozdzielić tę wywoływaną z bloku na inną funkcję albo dać jakąs flagę, się zobaczy
    go env' s = local (const env') $ checkStmtM s `throwExtraMsg` msg
        where msg e = [e, "in statement:", printTree s]

checkStmtM :: Stmt -> TCM TCEnv
checkStmtM Empty    = ask

checkStmtM (SExp e) = do
    _ <- checkExprM e
    ask

checkStmtM (Decl t ds) = do
    when (t == Void) $ throwTCM "Void variable declaration is forbidden"
    checkIfClassExists t
    env <- ask
    foldM go env ds
  where
    go :: TCEnv -> Item -> TCM TCEnv
    go acc d = local (const acc) $ handleDecl (typeToTCType t) d

    handleDecl :: TCType -> Item -> TCM TCEnv
    handleDecl t d = do
        var <- case d of
            (NoInit (Ident var)) -> return var
                -- case t of -- nie ma już funkcji do zadekl, wszystko może być domyślne
                -- (TDFun _ _) -> throwMsg
                --     [var, ": Default function declaration is forbidden"]
                -- _ -> return var
            (Init (Ident var) e) -> matchExpType t e >> return var -- TODO: czy dla klas to wystarcza?
        checkIfNameAlreadyInScope var

        scope <- asks scope
        env   <- ask
        let envWithDecl = insert var (t, scope) (types env)
        return $ env { types = envWithDecl }

checkStmtM (BStmt (Block ss)) = do
    env <- ask
    s   <- asks scope
    local (\env -> env { scope = s + 1 }) (checkStmtsM ss)
    ask

checkStmtM (Ass assignable e) = do
    case assignable of
        (EVar (Ident var)) -> do
            t <- getVarType var
            matchExpType t e
        (EArrAcc accessible index) -> do -- TODO: w tym arrAcc są Expr7!!!!
            (TArr t) <- matchExpType undefinedArrType accessible
            matchExpType TInt index
            matchExpType t    e
        (EAttrAcc accessible attr) -> undefined
    ask

checkStmtM (     Incr e   ) = checkIncrDecr e
checkStmtM (     Decr e   ) = checkIncrDecr e

checkStmtM stmt@(While e s) = do
    matchExpType TBool e --`throwExtraMsg` msg
    checkStmtM s
    ask

checkStmtM stmt@(Cond e s) = do
    matchExpType TBool e --`throwExtraMsg` msg
    checkStmtM s
    ask
  --  where msg e = [e, "\nin if statement:", printTree stmt]

checkStmtM stmt@(CondElse e s1 s2) = do
    matchExpType TBool e -- `throwExtraMsg` msg
    checkStmtM s1
    checkStmtM s2
    ask
    -- where msg e = [e, "\nin if/else statement:", printTree stmt]

checkStmtM (For type_ (Ident iter) arr stmt) = do
    checkIfClassExists type_
    (TArr t) <- matchExpType undefinedArrType arr
    matchType [t] (typeToTCType type_)

    s   <- asks scope
    env <- ask
    let typesWithIter = insert iter (t, s + 1) (types env)
    case stmt of
        (BStmt ss) ->
            local (\env -> env { types = typesWithIter }) (checkStmtM stmt)
        _ -> local (\env -> env { scope = s + 1, types = typesWithIter })
                   (checkStmtM stmt)
    ask



-- unchecked BEGIN
-- TODO: po ogarnięciu FnDef TopDefów
checkStmtM VRet    = matchReturn TVoid
checkStmtM (Ret e) = matchReturn =<< checkExprM e

matchReturn :: TCType -> TCM TCEnv
matchReturn t = do
    ex <- asks expectedRet
    case ex of
        Nothing           -> throwTCM "Return outside of function"
        (Just (eT, name)) -> matchType [eT] t `throwExtraMsg` msg name
    ask
    where msg name e = [name, ":", e, "in function return"]
-- unchecked END

checkIncrDecr :: Expr -> TCM TCEnv
checkIncrDecr assignable = do
    case assignable of
        (EVar (Ident var)) -> do
            t <- getVarType var
            matchType [TInt] t
            ask
        (EArrAcc accessible index) -> do -- TODO: w tym arrAcc są Expr7!!!!
            matchExpType (TArr TInt) accessible
            matchExpType TInt        index
            ask
        (EAttrAcc accessible attr) -> undefined
    -- ask

    -- t <- getVarType var
    -- matchType [TInt] t `throwExtraMsg` msg
    -- ask
    -- where msg e = [e, "in statement:", printTree stmt]


--- EXPRS -----------------------------------------------------------------

checkExprM :: Expr -> TCM TCType
checkExprM (ECastNull ident@(Ident cls)) = do
    checkIfClassExists (Cls ident)
    return (TDClass cls)
checkExprM (EVar    (Ident var)) = getVarType var

checkExprM (EString _          ) = return TString
checkExprM (ELitInt _          ) = return TInt
checkExprM ELitTrue              = return TBool
checkExprM ELitFalse             = return TBool

checkExprM (  Not e           )  = matchExpType TBool e
checkExprM (  Neg e           )  = matchExpType TInt e

checkExprM e@(EMul e1 _     e2)  = checkBinOp [TInt] e1 e2
checkExprM e@(EAdd e1 Plus  e2)  = checkBinOp [TInt, TString] e1 e2
checkExprM e@(EAdd e1 Minus e2)  = checkBinOp [TInt] e1 e2

-- TODO: czy ma być EQU/NE na obiektach i tablicach? chyba nie nie? plz no
checkExprM e@(ERel e1 EQU e2) =
    checkBinOp [TInt, TString, TBool] e1 e2 >> return TBool
checkExprM e@(ERel e1 NE e2) =
    checkBinOp [TInt, TString, TBool] e1 e2 >> return TBool

checkExprM e@(ERel e1 _ e2) = checkBinOp [TInt] e1 e2 >> return TBool
checkExprM e@(EAnd e1 e2) = checkBinOp [TBool] e1 e2
checkExprM e@(EOr e1 e2) = checkBinOp [TBool] e1 e2


checkExprM (ENew cls@(Cls (Ident clsName)) ClsNotArr) = do
    checkIfClassExists cls
    return $ TDClass clsName
checkExprM (ENew type_ (ArrSize sizeExpr)) = do
    checkIfClassExists type_ -- doesn't have to be a class, that's ok
    matchExpType TInt sizeExpr
    return $ TArr $ typeToTCType type_
checkExprM e@(ENew _ _) = throwMsg ["Illegal `new` expression: ", printTree e]
checkExprM (EAttrAcc expr ident) = undefined
-- TODO: jak się odwołuję poza tablicę, ale to raczej już później, bo w typechecku chyba nie mogę?
checkExprM (EArrAcc expr1 expr2) = do
    (TArr act) <- matchExpType undefinedArrType expr1
    matchExpType TInt expr2
    return act
checkExprM (EMethCall expr ident exprs) = undefined
checkExprM (EApp ident exprs          ) = undefined


matchExpType :: TCType -> Expr -> TCM TCType
matchExpType ex e
    | ex == undefinedArrType = do
        act <- checkExprM e
        case act of
            (TArr type_) -> return act
            _            -> throwMsg
                [ "Expected array type\nActual type:"
                , show act
                , "\nin expression: "
                , printTree e
                ]
        return act
    | otherwise = do
        act <- checkExprM e
        when (ex /= act) $ throwMsg
            [ "Expected type:"
            , show ex
            , "\nActual type:"
            , show act
            , "\nin expression: "
            , printTree e
            ]
        return act

-- matchExpType undefinedArrType e = do
--     act <- checkExprM e
--     case act of
--         (TArr type_) -> return act
--         _            -> throwMsg
--             [ "Expected array type\nActual type:"
--             , show act
--             , "\nin expression: "
--             , printTree e
--             ]
--     return act


-- matchExpType ex e = do
--     act <- checkExprM e
--     when (ex /= act) $ throwMsg
--         [ "Expected type:"
--         , show ex
--         , "\nActual type:"
--         , show act
--         , "\nin expression: "
--         , printTree e
--         ]
--     return act

checkBinOp :: [TCType] -> Expr -> Expr -> TCM TCType
checkBinOp ts e1 e2 = do
    e1T <- checkExprM e1
    matchType ts e1T
    matchType [e1T] =<< checkExprM e2
    return e1T

  --  msg err = [err, "\nIn:", printTree expr]

matchType :: [TCType] -> TCType -> TCM ()
matchType [ex] act = when (ex /= act)
    $ throwMsg ["Expected type:", show ex, "\nActual type:", show act]
matchType exs act = when (act `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show act]
