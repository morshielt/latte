module StaticAnalysis
    ( runStaticAnalysis
    )
where


import           AbsLatte

import           SATypes
import           SAUtils
import           PrintLatte

import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data.List                      ( intercalate )
import           Data.Map                      as M
                                                ( Map
                                                , union
                                                , insert
                                                , fromList
                                                , empty
                                                , lookup
                                                , adjust
                                                , null
                                                , delete
                                                , partition
                                                , toList
                                                , showTree
                                                )

import           Control.Monad                  ( when )
-- TODO: CHECK RETURNS
-- TODO: czy main ma dobry typ i czy istnieje!

-- TODO: posprawdzać jak wyglądają error message


-- TODO: czy metody obiektów mają returny
-- TODO: to chyba też już nie w typechecku
-- int[][] arr = new int[][20];
-- arr[1] = 5; -- TODO: co tu w ogóle można przypisać? tablicę odp. długości czy nic czy co????

-- TODO: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?

-- TODO: check if main present
-- TODO: cykliczne `extends`

-- TODO: KLASY BADZIEWNE MENDY
-- TODO:  EMethCall EAttrAcc: muszą ogarniać, że z nadklas można mieć atr/met
-- TODO:  Decl Ass: można przypisywać na zmienną typu nadklasy elem typu podklasy
-- TODO: że atrybuty w podkl/nadkl się nie powtarzają, a metody mogą, jeśli mają zgodne typy

-- TODO: jak się odwołuję poza tablicę, ale to raczej już później, bo w typechecku chyba nie mogę?


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

    go :: [TopDef] -> TCM TCEnv
    go prog = do
        env    <- ask
        env'   <- foldM saveTopDefTypes env prog
        env''  <- local (const env') (saveClassesMembers prog)
        env''' <- local (const env'') (checkClassDefsM prog)
        local (const env''') (checkFnDefsM prog)

saveTopDefTypes :: TCEnv -> TopDef -> TCM TCEnv
saveTopDefTypes env td = local (const env) $ saveTopDef td
  where
    saveTopDef :: TopDef -> TCM TCEnv
    saveTopDef (FnDef ret (Ident name) args _) = do
        checkIfNameAlreadyInScope name
        t   <- typeToTCType $ Fun ret (map (\(Arg t _) -> t) args)
        env <- ask
        return $ env { types = M.insert name (t, initScope) (types env) }
    saveTopDef (ClDef (Ident clsName) classext _) = do
        clsDef <- getClassDef clsName
        case clsDef of
            Nothing -> do
                let extends = extractExt classext
                let clsDef  = ClassDef { extends = extends, members = M.empty }
                env <- ask
                return $ env { classes = M.insert clsName clsDef (classes env) }
            _ -> throwTCM $ "Class `" ++ clsName ++ "` already declared"
      where
        extractExt :: ClassExt -> Maybe Var
        extractExt ext = case ext of
            NoExt              -> Nothing
            Ext (Ident parent) -> Just parent

saveClassesMembers :: [TopDef] -> TCM TCEnv
saveClassesMembers ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ saveClassMembers s

    saveClassMembers :: TopDef -> TCM TCEnv
    saveClassMembers FnDef{}                           = ask
    saveClassMembers (ClDef (Ident ident) _ clmembers) = do
        env  <- ask
        env' <- foldM (go' ident) env clmembers
        return $ env { classes = classes env' }
      where
        go' :: Var -> TCEnv -> ClMember -> TCM TCEnv
        go' ident env cmembers =
            local (const env)
            $               saveClassMember ident cmembers
            `throwExtraMsg` msg
            where msg e = [e, " in class `", ident, "`"]

        saveClassMember :: Var -> ClMember -> TCM TCEnv
        saveClassMember cls member = case member of
            Attr type_ (Ident ident)      -> saveClassMember' cls ident type_
            Meth ret (Ident ident) args _ -> saveClassMember' cls ident
                $ Fun ret (map (\(Arg t _) -> t) args)
          where
            saveClassMember' :: Var -> Var -> Type -> TCM TCEnv
            saveClassMember' cls ident type_ = do
                env    <- ask
                clsDef <- getSureClassDef cls
                checkIfMemberExists (members clsDef) ident
                t <- typeToTCType type_
                let clsDef' = clsDef
                        { members = M.insert ident t $ members clsDef
                        }
                return $ env { classes = M.insert cls clsDef' (classes env) }
              where
                checkIfMemberExists :: M.Map Var TCType -> Var -> TCM ()
                checkIfMemberExists mmbrs name = case M.lookup name mmbrs of
                    Nothing -> return ()
                    _ -> throwTCM $ "member `" ++ name ++ "` already declared"

checkClassDefsM :: [TopDef] -> TCM TCEnv
checkClassDefsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ checkClassDefM s

    checkClassDefM :: TopDef -> TCM TCEnv
    checkClassDefM FnDef{} = ask
    checkClassDefM (ClDef (Ident ident) classext clmembers) = do
        env  <- ask
        env' <- foldM (goAddAttrsToEnv ident) env clmembers
        foldM_ (goCheckMethods ident) env' clmembers
        ask
      where
        msg e = [e, " in class `", ident, "`"]

        goAddAttrsToEnv :: Var -> TCEnv -> ClMember -> TCM TCEnv
        goAddAttrsToEnv ident env cmembers =
            local (const env) $ addAttrsToEnv ident cmembers `throwExtraMsg` msg
          where
            addAttrsToEnv :: Var -> ClMember -> TCM TCEnv
            addAttrsToEnv cls Meth{}                     = ask
            addAttrsToEnv cls (Attr type_ (Ident ident)) = do
                clsDef <- getSureClassDef cls
                t      <- typeToTCType type_
                env    <- ask
                return env
                    { types = M.insert ident (t, initScope + 1) $ types env
                    }

        goCheckMethods :: Var -> TCEnv -> ClMember -> TCM TCEnv
        goCheckMethods ident env cmembers =
            local (const env) $ checkMethods ident cmembers `throwExtraMsg` msg
          where
            checkMethods :: Var -> ClMember -> TCM TCEnv
            checkMethods cls Attr{}                             = ask
            checkMethods cls x@(Meth ret (Ident ident) args bs) = do
                env    <- ask
                clsDef <- getSureClassDef cls

                case extends clsDef of
                    Nothing       -> return ()
                    (Just parent) -> do
                        parentDef <- getSureClassDef parent
                        case M.lookup ident $ members parentDef of
                            Nothing -> return ()
                            (Just parentMemberType) ->
                                case M.lookup ident $ members clsDef of
                                    Nothing ->
                                        throwTCM "IMSPOIBLEEEEEEEEE TODO"
                                    (Just memberType) -> do
                                        -- liftIO $ putStrLn $ show parentMemberType
                                        -- liftIO $ putStrLn $ show memberType
                                        matchType [parentMemberType] memberType
                                        return ()
                -- liftIO $ putStrLn $ show x

                ret'      <- typeToTCType ret
                -- TODO : set return
                argsTypes <- handleArgs args
                let
                    env' = env
                        { types = M.insert "self" (TDClass cls, scope env + 1)
                                  $       argsTypes
                                  `union` types env
                        , expectedRet =
                            Just
                                ( ret'
                                , "class `"
                                ++ cls
                                ++ "` method `"
                                ++ ident
                                ++ "`"
                                )
                        }
                local (const env') $ checkStmtM $ BStmt bs
                ask

handleArgs :: [Arg] -> TCM Types
handleArgs args = do
    scope <- asks scope
    list  <- mapM
        (\(Arg t (Ident var)) -> do
            t' <- typeToTCType t
            if t' == TVoid
                then throwTCM "Illegal void function parameter TODO msg"
                else return (var, (t', scope + 1)) -- TODO: check czy na pewno wszystko co używa `handleArgs` jest BStmt i robi scope +1
        )
        args
    let mapList = fromList list
    if length list == length mapList
        then return mapList
        else throwTCM "Function arguments must have different names"

-- TODO: jaki jest default decl klasy rekurencyjnej? (list atrybutem list)
-- TODO : sprawdzać czy nazwy memberów się nie powtarzają

checkFnDefsM :: [TopDef] -> TCM TCEnv
checkFnDefsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ checkFnDefM s

checkFnDefM :: TopDef -> TCM TCEnv
checkFnDefM ClDef{}                          = ask
checkFnDefM (FnDef ret (Ident name) args bs) = do
    ret'      <- typeToTCType ret
    env       <- ask
    argsTypes <- handleArgs args
-- TODO : set return
-- TODO : dodać argumenty do enva przy sprawdzaniu funkcji
    let env' = env { types       = argsTypes `union` types env
                   , expectedRet = Just (ret', name)
                   }
    local (const env') $ checkStmtM (BStmt bs) `throwExtraMsg` msg
    ask
    where msg e = [e, " in function `", name, "`"]


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
        where msg e = [e, "in statement:\n", printTree s]

checkStmtM :: Stmt -> TCM TCEnv
checkStmtM Empty    = ask

checkStmtM (SExp e) = do
    _ <- checkExprM e `throwExtraMsg` msg
    ask
    where msg er = [er, "in expression:\n", printTree e]

checkStmtM (Decl t ds) = do
    when (t == Void) $ throwTCM "Void variable declaration is forbidden"
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
                -- case t of -- nie ma już funkcji do zadekl, wszystko może być domyślne
                -- (TDFun _ _) -> throwMsg
                --     [var, ": Default function declaration is forbidden"]
                -- _ -> return var
            (Init (Ident var) e) -> case t of
                (TDClass cls) -> matchParentClasses cls e >> return var
                _             -> matchExpType t e >> return var -- TODO: czy dla klas to wystarcza?
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
    t <- checkExprM assignable `throwExtraMsg` msg
    case t of
        (TDClass cls) -> matchParentClasses cls e
        _             -> do
            matchExpType t e
            ask
    where msg er = [er, "in expression:\n", printTree e]

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

checkStmtM (     Incr e                         ) = checkIncrDecr e
checkStmtM (     Decr e                         ) = checkIncrDecr e

checkStmtM stmt@(While e s                      ) = checkWhileIf e [s]
checkStmtM stmt@(Cond  e s                      ) = checkWhileIf e [s]
checkStmtM stmt@(CondElse e s1 s2               ) = checkWhileIf e [s1, s2]


checkStmtM (     For type_ (Ident iter) arr stmt) = do
    checkIfClassExistsT type_
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

checkWhileIf :: Expr -> [Stmt] -> TCM TCEnv
checkWhileIf e [s] = matchExpType TBool e >> checkStmtM s >> ask
checkWhileIf e [s1, s2] =
    matchExpType TBool e >> checkStmtM s1 >> checkStmtM s2 >> ask
checkWhileIf _ _ =
    throwTCM
        "Impossible - while/if has at least 1 and at most 2 statements to check."

checkIncrDecr :: Expr -> TCM TCEnv
checkIncrDecr e = checkExprM e >>= matchType [TInt] >> ask

--- EXPRS -----------------------------------------------------------------

checkExprM :: Expr -> TCM TCType
checkExprM (ECastNull ident@(Ident cls)) =
    checkIfClassExistsT (Cls ident) >> return (TDClass cls)
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

-- TODO: czy ma być EQU/NE na obiektach i tablicach? z nullem ma być
checkExprM e@(ERel e1 EQU e2) =
    checkBinOp [TInt, TString, TBool, wildcardClass] e1 e2 >> return TBool
checkExprM e@(ERel e1 NE e2) =
    checkBinOp [TInt, TString, TBool, wildcardClass] e1 e2 >> return TBool

checkExprM e@(ERel e1 _ e2) = checkBinOp [TInt] e1 e2 >> return TBool
checkExprM e@(EAnd e1 e2  ) = checkBinOp [TBool] e1 e2
checkExprM e@(EOr  e1 e2  ) = checkBinOp [TBool] e1 e2


checkExprM (ENew (Cls (Ident clsName)) ClsNotArr) =
    checkIfClassExists clsName >> return (TDClass clsName)
checkExprM (ENew type_ (ArrSize sizeExpr)) = do
    checkIfClassExistsT type_ -- doesn't have to be a class, that's ok
    matchExpType TInt sizeExpr
    TArr <$> typeToTCType type_
checkExprM e@(ENew _ _) =
    throwTCM $ "Illegal `new` expression: " ++ printTree e
checkExprM (EArrAcc expr1 expr2) = do
    (TArr act) <- matchExpType undefinedArrType expr1
    matchExpType TInt expr2
    return act
checkExprM (EAttrAcc expr (Ident ident))
    | ident == "length" = do
        type_ <- matchExpType undefinedArrType expr
        case type_ of
            (TArr _) -> return TInt
            _        -> checkEAttrAcc
    | otherwise = checkEAttrAcc
  where
    checkEAttrAcc = do
        (TDClass clsName) <- matchExpType wildcardClass expr -- TODO: nigdy się teoretycznie nie powinno wywalić, bo matchExpType rzuca jc
        matchAttr clsName
      where
        matchAttr clsName = do
            classes <- asks classes
            case M.lookup clsName classes of
                Nothing       -> throwTCM "3IMPOSSIBLE ERROR, IT HAS TO EXIST"
                (Just clsDef) -> case M.lookup ident (members clsDef) of
                    Nothing -> case extends clsDef of
                        Nothing     -> throwTCM "NO such attribute TODO msg"
                        Just parent -> matchAttr parent
                    (Just (TDFun _ _)) ->
                        throwTCM "It's a method not an attribute TODO msg"
                    (Just t) -> return t

checkExprM e@(EMethCall expr (Ident ident) es) = do
    (TDClass clsName) <- matchExpType wildcardClass expr -- TODO: nigdy się teoretycznie nie powinno wywalić, bo matchExpType rzuca jc
    matchMethod clsName
  where
    matchMethod clsName = do
        classes <- asks classes
        case M.lookup clsName classes of
            Nothing       -> throwTCM "4IMPOSSIBLE ERROR, IT HAS TO EXIST"
            (Just clsDef) -> case M.lookup ident (members clsDef) of
                Nothing -> case extends clsDef of
                    Nothing     -> throwTCM "NO such method TODO msg"
                    Just parent -> matchMethod parent
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
        matchType [ex] act
        -- when (ex /= act) $ throwMsg
        --     [ "Expected type:"
        --     , show ex
        --     , "\nActual type:"
        --     , show act
        --     , "\nin expression: "
        --     , printTree e
        --     ]
        return act

checkBinOp :: [TCType] -> Expr -> Expr -> TCM TCType
checkBinOp ts e1 e2 = do
    e1T <- checkExprM e1
    matchType ts e1T
    matchType [e1T] =<< checkExprM e2
    return e1T

--TODO: może tu też trzeba klasy pasowalne ogarniać?
matchType :: [TCType] -> TCType -> TCM ()
matchType [ex] act = when (ex /= act)
    $ throwMsg ["Expected type:", show ex, "\nActual type:", show act]
matchType exs cls@(TDClass _) = when (wildcardClass `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show cls]
matchType exs act = when (act `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show act]


matchParentClasses :: Var -> Expr -> TCM TCEnv
matchParentClasses clsParent e = do
    t2 <- checkExprM e
    case t2 of
        (TDClass cls) -> do
            compatibles <- getCompatibleClasses cls
            if clsParent `notElem` compatibles
                then
                    throwTCM
                        "TODO msg incompatible types (incompatible unrelated classes)"
                else ask
        _ -> throwTCM "TODO msg incompatible types (expected class got sth)"
  where
    getCompatibleClasses :: Var -> TCM [Var]
    getCompatibleClasses cls = getCompatibles [cls] cls
    getCompatibles :: [Var] -> Var -> TCM [Var]
    getCompatibles compatible cls = do
        p <- getClassParent cls
        case p of
            Nothing       -> return compatible
            (Just parent) -> getCompatibles (parent : compatible) parent
