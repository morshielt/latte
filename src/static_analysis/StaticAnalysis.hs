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
import           Data.Map                      as M
                                                ( Map
                                                , union
                                                , insert
                                                , fromList
                                                , empty
                                                , lookup
                                                )

import           Control.Monad                  ( when )

-- TODO: czy metody obiektów mają returny
-- TODO: to chyba też już nie w typechecku
-- int[][] arr = new int[][20];
-- arr[1] = 5; -- TODO: co tu w ogóle można przypisać? tablicę odp. długości czy nic czy co????

-- TODO: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?

-- TODO: check if main present
-- TODO: cykliczne `extends`
-- TODO : do BStmt chyba potrzebuję jednak Reader monad? tak jest.

initScope = 0


runStaticAnalysis (Program prog) = runReaderT (go prog)
    $ TCEnv initialTypes M.empty initScope Nothing
  where
    initialTypes :: M.Map Var (TCType, Scope)
    initialTypes = M.fromList
        [ ("printInt"   , (TDFun [TInt] TVoid, initScope))
        , ("printString", (TDFun [TString] TVoid, initScope))
        , ("error"      , (TDFun [] TVoid, initScope))
        , ("readInt"    , (TDFun [] TInt, initScope))
        , ("readString" , (TDFun [] TString, initScope))
        ]

    saveTopDefTypes :: TCEnv -> TopDef -> TCM TCEnv
    saveTopDefTypes acc td =
        local (const acc) $ handleTopDef td `throwExtraMsg` msg td
      where
        msg td e = ["function", e, " ", printTree td] -- TODO: BETTER MESSAGE + TODO: msg for 'print' 'error' etc.
        handleTopDef :: TopDef -> TCM TCEnv
        handleTopDef (ClDef (Ident clsName) classext clmembers) = do
            clsDef <- getClassDef clsName
            case clsDef of
                Nothing -> do
                    let extends = case classext of
                            NoExt              -> Nothing
                            Ext (Ident parent) -> Just parent
                    env <- ask
                    return $ env
                        { classes = M.insert
                                        clsName
                                        (ClassDef { extends = extends
                                                  , members = M.empty
                                                  }
                                        )
                                        (classes env)
                        }
                _ -> throwTCM $ "Class `" ++ clsName ++ "` already declared"

        handleTopDef (FnDef ret (Ident name) args _) = do
            checkIfNameAlreadyInScope name
            t   <- typeToTCType $ Fun ret (map (\(Arg t _) -> t) args)
            -- let
            --     t = TDFun (map (\(Arg t _) -> typeToTCType t) args)
            --         $ typeToTCType ret
            env <- ask
            return $ env { types = M.insert name (t, initScope) (types env) }

    go :: [TopDef] -> TCM TCEnv
    go prog = do
        env   <- ask
        env'  <- foldM saveTopDefTypes env prog
        env'' <- local (const env') (checkClassDefsM prog)
        local (const env'') (checkFnDefsM prog)
        -- checkReturns prog

-- TODO: ^może nawet tu wyżej w runStaticAnalysis taki init mapy dać!!!
-- TODO: ^jedno przejście po topdefach dodać tylko że dane funkcje/klasy istnieją, żeby potem w środku było, że są!!!
checkClassDefsM :: [TopDef] -> TCM TCEnv
checkClassDefsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ checkClassDefM s

-- TODO: łapanie errorów w topdefach i jakieś ładniejsze message
checkClassDefM :: TopDef -> TCM TCEnv
checkClassDefM (FnDef ret (Ident name) args (Block stmts)) = ask
checkClassDefM (ClDef (Ident ident) classext clmembers   ) = do
    env <- ask
-- TODO : czy istnieje parent TODO: ładny message, że nie istenieje
    case classext of
        NoExt       -> return ()
        (Ext ident) -> checkIfClassExists (Cls ident)
-- TODO : dodać atrybuty jako zmienne w tym scope
    env' <- foldM (go ident) env clmembers
    foldM_ (go2 ident) env' clmembers
-- TODO : i uzupełnić memberów w mapie `classes`
    return $ env { classes = classes env' }
  where
    go2 :: Var -> TCEnv -> ClMember -> TCM TCEnv
    go2 ident env1 cmem = local (const env1) $ checkMethods ident cmem
    go :: Var -> TCEnv -> ClMember -> TCM TCEnv
    go ident env1 cmem = local (const env1) $ handleClsMember ident cmem


-- TODO: wywołanie funkcji zewnetrznej w memberze
-- FACT: nie ma rekurencyjnego wywoływania metod TODO: czy musi być?
checkMethods :: Var -> ClMember -> TCM TCEnv
checkMethods cls (Attr type_ (Ident ident)      ) = ask
checkMethods cls (Meth ret (Ident ident) args bs) = do
    ret'      <- typeToTCType ret
    env       <- ask
    -- TODO : set return
    argsTypes <- handleArgs args
    let
        env' = env
            { types       = argsTypes `union` types env
            , expectedRet =
                Just (ret', "class `" ++ cls ++ "` method `" ++ ident ++ "`")
            }
    local (const env') $ checkStmtM $ BStmt bs
    ask

handleArgs :: [Arg] -> TCM Types
handleArgs args = do
    scope <- asks scope
    list  <- mapM
        (\(Arg t (Ident var)) -> do
            t' <- typeToTCType t
            return (var, (t', scope + 1)) -- TODO: check czy na pewno wszystko co używa `handleArgs` jest BStmt i robi scope +1
        )
        args
    let mapList = fromList list
    if length list == length mapList
        then return mapList
        else throwTCM "Function arguments must have different names"

-- TODO: jaki jest default decl klasy rekurencyjnej? (list atrybutem list)
-- TODO : sprawdzać czy nazwy memberów się nie powtarzają
handleClsMember :: Var -> ClMember -> TCM TCEnv
handleClsMember cls (Attr type_ (Ident ident)) = do
    env <- ask
    case M.lookup cls $ classes env of
        Nothing       -> throwTCM "IMPOSSIBLE ERROR TODO"
        (Just clsDef) -> do
            checkIfMemberExists (members clsDef) ident
            t <- typeToTCType type_
            let clsDef' =
                    clsDef { members = M.insert ident t $ members clsDef }
            let
                env' = env
                    { types = M.insert ident (t, initScope + 1) $ types env
                    } -- TODO: initScope + 1, gurl, zgubisz się (pewnie już się zgubiłaś, ciiiii)
            return $ env' { classes = M.insert cls clsDef' (classes env) }

handleClsMember cls (Meth ret (Ident ident) args _) = do
    env <- ask
    case M.lookup cls $ classes env of
        Nothing       -> throwTCM "IMPOSSIBLE ERROR TODO"
        (Just clsDef) -> do
            checkIfMemberExists (members clsDef) ident
            t <- typeToTCType $ Fun ret (map (\(Arg t _) -> t) args)
            let clsDef' =
                    clsDef { members = M.insert ident t $ members clsDef }
            return $ env { classes = M.insert cls clsDef' (classes env) }

checkIfMemberExists :: M.Map Var TCType -> Var -> TCM ()
checkIfMemberExists mmbrs name = case M.lookup name mmbrs of
    Nothing -> return ()
    _       -> throwTCM $ "member `" ++ name ++ "` already declared"


checkFnDefsM :: [TopDef] -> TCM TCEnv
checkFnDefsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ checkFnDefM s

checkFnDefM :: TopDef -> TCM TCEnv
checkFnDefM (ClDef (Ident ident) classext clmembers) = ask
checkFnDefM (FnDef ret (Ident name) args bs        ) = do
    ret'      <- typeToTCType ret
    env       <- ask
    argsTypes <- handleArgs args
-- TODO : set return
-- TODO : dodać argumenty do enva przy sprawdzaniu funkcji
    let env' = env { types       = argsTypes `union` types env
                   , expectedRet = Just (ret', name)
                   }
    local (const env') $ checkStmtM (BStmt bs)
    ask


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
    go acc d = do
        t' <- typeToTCType t
        local (const acc) $ handleDecl t' d

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
        let envWithDecl = M.insert var (t, scope) (types env)
        return $ env { types = envWithDecl }

checkStmtM (BStmt (Block ss)) = do
    env <- ask
    s   <- asks scope
    local (\env -> env { scope = s + 1 }) (checkStmtsM ss)
    ask

checkStmtM (Ass assignable e) = do
    t <- checkExprM assignable
    matchExpType t e
    ask
-- checkStmtM (Ass assignable e) = do
--     case assignable of
--         (EVar (Ident var)) -> do
--             t <- getVarType var
--             matchExpType t e
--         (EArrAcc accessible index) -> do -- TODO: w tym arrAcc są Expr7!!!! no i co z tego?
--             (TArr t) <- matchExpType undefinedArrType accessible
--             matchExpType TInt index
--             matchExpType t    e
--         (EAttrAcc accessible attr) -> undefined
--     ask

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
    typeToTCType type_ >>= matchType [t]

    s   <- asks scope
    env <- ask
    let typesWithIter = M.insert iter (t, s + 1) (types env)
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
    t <- checkExprM assignable
    matchType [TInt] t
    ask

-- checkIncrDecr assignable = do
--     case assignable of
--         (EVar (Ident var)) -> do
--             t <- getVarType var
--             matchType [TInt] t
--             ask
--         (EArrAcc accessible index) -> do -- TODO: w tym arrAcc są Expr7!!!!
--             matchExpType (TArr TInt) accessible
--             matchExpType TInt        index
--             ask
--         (EAttrAcc accessible attr) -> undefined


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
    TArr <$> typeToTCType type_
checkExprM e@(ENew _ _) = throwMsg ["Illegal `new` expression: ", printTree e]
-- TODO: jak się odwołuję poza tablicę, ale to raczej już później, bo w typechecku chyba nie mogę?
checkExprM (EArrAcc expr1 expr2) = do
    (TArr act) <- matchExpType undefinedArrType expr1
    matchExpType TInt expr2
    return act
checkExprM (EAttrAcc expr (Ident ident)) = do
    (TDClass clsName) <- matchExpType wildcardClass expr -- TODO: nigdy się teoretycznie nie powinno wywalić, bo matchExpType rzuca jc
    classes           <- asks classes
    case M.lookup clsName classes of
        Nothing       -> throwTCM "IMPOSSIBLE ERROR, IT HAS TO EXIST"
        (Just clsDef) -> case M.lookup ident (members clsDef) of
            Nothing -> throwTCM "NO such attribute TODO msg"
            (Just (TDFun _ _)) ->
                throwTCM "It's a method not an attribute TODO msg"
            (Just t) -> return t

checkExprM (EMethCall expr (Ident ident) es) = do
    (TDClass clsName) <- matchExpType wildcardClass expr -- TODO: nigdy się teoretycznie nie powinno wywalić, bo matchExpType rzuca jc
    classes           <- asks classes
    case M.lookup clsName classes of
        Nothing       -> throwTCM "IMPOSSIBLE ERROR, IT HAS TO EXIST"
        (Just clsDef) -> case M.lookup ident (members clsDef) of
            Nothing                 -> throwTCM "NO such method TODO msg"
            (Just (TDFun args ret)) -> do
                checkArgs args es
                return ret
            (Just t) -> throwTCM "It's an attribute not a method TODO msg"

checkExprM (EApp (Ident var) es) = do
    typeScope <- getVarTypeScope var
    case typeScope of
        Nothing -> throwMsg ["function ", var, " is not declared"]
        (Just (TDFun args ret, _)) -> do
            checkArgs args es -- `throwExtraMsg` msg
            return ret
        (Just _) -> throwMsg [var, " is not a function"]

checkArgs :: [TCType] -> [Expr] -> TCM ()
checkArgs args es = if length args == length es
    then mapM_ checkArg $ zip args es
    else throwTCM "Invalid number of arguments in function call"
    where checkArg (t, e) = matchExpType t e

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
    | ex == wildcardClass = do
        act <- checkExprM e
        case act of
            (TDClass clsName) -> return act
            _                 -> throwMsg
                [ "Expected class type\nActual type:"
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
