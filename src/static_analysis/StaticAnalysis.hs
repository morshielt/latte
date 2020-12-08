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

-- TODO: czy metody obiektów mają returny
-- TODO: to chyba też już nie w typechecku
-- int[][] arr = new int[][20];
-- arr[1] = 5; -- TODO: co tu w ogóle można przypisać? tablicę odp. długości czy nic czy co????

-- TODO: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?

-- TODO: check if main present
-- TODO: cykliczne `extends`
-- TODO : do BStmt chyba potrzebuję jednak Reader monad? tak jest.

-- TODO: KLASY BADZIEWNE MENDY
-- TODO:  EMethCall EAttrAcc: muszą ogarniać, że z nadklas można mieć atr/met
-- TODO:  Decl Ass: można przypisywać na zmienną typu nadklasy elem typu podklasy
-- TODO: że atrybuty w podkl/nadkl się nie powtarzają, a metody mogą, jeśli mają zgodne typy


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
        env <- ask

        let (fnsTDs, classesTDs) = splitTDs prog
        env'   <- foldM saveTopDefTypes env prog

        -- mappu <- clsDefToMapEntries classesTDs
        -- let (bottomClasses, mappu') = partition (\(i, _, _) -> i == 0) mappu
        -- let bottomClasses' = map (\(k, (_, par, tdef)) -> (k, par, tdef))
        --         $ toList bottomClasses
        -- liftIO $ putStrLn $ showTree mappu'
        -- liftIO $ putStrLn $ show bottomClasses'
        -- topoOrderClasses <- topSort mappu' bottomClasses' []
        env''  <- local (const env') (saveClassMembers classesTDs) -- TODO: do in correct order!
        env''' <- local (const env'') (checkClassDefsM classesTDs) -- TODO: do in correct order!
        -- env'' <- local (const env') (checkClassDefsM prog) -- TODO: do in correct order!

        -- checkReturns prog
        local (const env''') (checkFnDefsM prog)
      where
        countExtends
            :: [TopDef]
            -> Map Var (Integer, Maybe Var, TopDef)
            -> TCM (Map Var (Integer, Maybe Var, TopDef))
        countExtends [] mappu = return mappu
        countExtends (tdef@(ClDef _ NoExt _) : tds) mappu =
            countExtends tds mappu
        countExtends (tdef@(ClDef _ (Ext (Ident parent)) _) : tds) mappu =
            case M.lookup parent mappu of
                Nothing ->
                    throwTCM $ "No such class named `" ++ parent ++ "` declared"
                _ -> countExtends tds $ adjust incrInMap parent mappu
        clsDefToMapEntries
            :: [TopDef] -> TCM (Map Var (Integer, Maybe Var, TopDef))
        clsDefToMapEntries tds =
            clsDefToMapEntries' tds [] >>= countExtends tds
        clsDefToMapEntries'
            :: [TopDef]
            -> [(Var, (Integer, Maybe Var, TopDef))]
            -> TCM (Map Var (Integer, Maybe Var, TopDef))
        clsDefToMapEntries' [] l = return $ M.fromList l
        clsDefToMapEntries' (tdef@(ClDef (Ident clsName) (Ext (Ident parent)) clmembers) : tds) l
            = clsDefToMapEntries' tds ((clsName, (0, Just parent, tdef)) : l)
        clsDefToMapEntries' (tdef@(ClDef (Ident clsName) NoExt clmembers) : tds) l
            = clsDefToMapEntries' tds ((clsName, (0, Nothing, tdef)) : l)

        splitTDs :: [TopDef] -> ([TopDef], [TopDef])
        splitTDs prog = splitTDs2 prog [] []
        splitTDs2 :: [TopDef] -> [TopDef] -> [TopDef] -> ([TopDef], [TopDef])
        splitTDs2 (f@FnDef{} : tds) fns clss = splitTDs2 tds (f : fns) clss
        splitTDs2 (c@ClDef{} : tds) fns clss = splitTDs2 tds fns (c : clss)
        -- splitTDs2 []                fns clss = (fns, topoSort clss)
        splitTDs2 []                fns clss = (fns, clss)

        topSort
            :: Map Var (Integer, Maybe Var, TopDef)
            -> [(Var, Maybe Var, TopDef)]
            -> [TopDef]
            -> TCM [TopDef]
        topSort graph [] l
            | M.null graph = return l
            | otherwise    = throwTCM "Cyclic class inheritance TODO msg"
        topSort graph ((curr, Nothing, td) : ss) l = topSort graph ss (td : l)
        topSort graph ((curr, Just parent, td) : ss) l = do
            let graph' = adjust decrInMap parent graph
            case M.lookup parent graph' of
                Just (ctr, ppar, def) -> if ctr == 0
                    then topSort (delete parent graph')
                                 ((parent, ppar, def) : ss)
                                 (td : l)
                    else topSort graph' ss (td : l)
                Nothing -> throwTCM "How could that even be possible TODO msg"

        incrInMap, decrInMap
            :: (Integer, Maybe Var, TopDef) -> (Integer, Maybe Var, TopDef)
        decrInMap (i, par, def) = (i - 1, par, def)
        incrInMap (i, par, def) = (i + 1, par, def)


-- L ← Empty list that will contain the sorted elements
-- S ← Set of all nodes with no incoming edge

-- while S is not empty do
--     remove a node n from S
--     add n to L
--     for each node m with an edge e from n to m do
--         remove edge e from the graph
--         if m has no other incoming edges then
--             insert m into S

-- if graph has edges then
--     return error   (graph has at least one cycle)
-- else 
--     return L   (a topologically sorted order)


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

-- TODO: ^może nawet tu wyżej w runStaticAnalysis taki init mapy dać!!!
-- TODO: ^jedno przejście po topdefach dodać tylko że dane funkcje/klasy istnieją, żeby potem w środku było, że są!!!

checkClassDefsM :: [TopDef] -> TCM TCEnv
checkClassDefsM ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ checkClassDefM s


saveClassMembers :: [TopDef] -> TCM TCEnv
saveClassMembers ss = do
    env <- ask
    foldM go env ss
  where
    go :: TCEnv -> TopDef -> TCM TCEnv
    go env' s = local (const env') $ saveClassMember s

saveClassMember :: TopDef -> TCM TCEnv
saveClassMember (FnDef ret (Ident name) args (Block stmts)) = ask
saveClassMember (ClDef (Ident ident) classext clmembers   ) = do
    env  <- ask
    env' <- foldM (go ident) env clmembers
    return $ env { classes = classes env' }
  where
    go :: Var -> TCEnv -> ClMember -> TCM TCEnv
    go ident env1 cmem = local (const env1) $ saveClsMember ident cmem

    saveClsMember :: Var -> ClMember -> TCM TCEnv
    saveClsMember cls (Attr type_ (Ident ident)) = do
        env <- ask
        case M.lookup cls $ classes env of
            Nothing       -> throwTCM "1IMPOSSIBLE ERROR TODO"
            (Just clsDef) -> do
                checkIfMemberExists (members clsDef) ident
                t <- typeToTCType type_
                let clsDef' = clsDef
                        { members = M.insert ident t $ members clsDef
                        }
                return $ env { classes = M.insert cls clsDef' (classes env) }

    saveClsMember cls (Meth ret (Ident ident) args _) = do
        env <- ask
        case M.lookup cls $ classes env of
            Nothing       -> throwTCM "2IMPOSSIBLE ERROR TODO"
            (Just clsDef) -> do
                checkIfMemberExists (members clsDef) ident
                t <- typeToTCType $ Fun ret (map (\(Arg t _) -> t) args)
                let clsDef' = clsDef
                        { members = M.insert ident t $ members clsDef
                        }
                return $ env { classes = M.insert cls clsDef' (classes env) }


checkIfMemberExists :: M.Map Var TCType -> Var -> TCM ()
checkIfMemberExists mmbrs name = case M.lookup name mmbrs of
    Nothing -> return ()
    _       -> throwTCM $ "member `" ++ name ++ "` already declared"



-- TODO: łapanie errorów w topdefach i jakieś ładniejsze message
checkClassDefM :: TopDef -> TCM TCEnv
checkClassDefM (FnDef ret (Ident name) args (Block stmts)) = ask
checkClassDefM (ClDef (Ident ident) classext clmembers   ) = do
    env  <- ask
-- TODO : czy istnieje parent TODO: ładny message, że nie istenieje
-- TODO: cykliczne extends
    -- case classext of
    --     NoExt                  -> ask
    --     (Ext p@(Ident parent)) -> do
    --         checkIfClassExistsT (Cls p)
    --         checkExtends parent
-- TODO : dodać atrybuty jako zmienne w tym scope
    env' <- foldM (go ident) env clmembers
    foldM_ (go2 ident) env' clmembers
-- TODO : i uzupełnić memberów w mapie `classes`
    -- return $ env { classes = classes env' }
    ask
  where
    go :: Var -> TCEnv -> ClMember -> TCM TCEnv
    go ident env1 cmem = local (const env1) $ handleClsMember ident cmem
    go2 :: Var -> TCEnv -> ClMember -> TCM TCEnv
    go2 ident env1 cmem = local (const env1) $ checkMethods ident cmem

    -- checkExtends :: Var -> TCM TCEnv
    -- checkExtends cls = checkIfExtendsAcyclic [cls] cls

    -- checkIfExtendsAcyclic :: [Var] -> Var -> TCM TCEnv
    -- checkIfExtendsAcyclic visited cls = do
    --     maybeParent <- getClassParent cls
    --     case maybeParent of
    --         Nothing       -> ask
    --         (Just parent) -> if parent `elem` visited
    --             then
    --                 throwTCM $ "CYCLIC CLASS EXTENDS TODO msg: " ++ show visited
    --             else checkIfExtendsAcyclic (parent : visited) parent

handleClsMember :: Var -> ClMember -> TCM TCEnv
handleClsMember cls (Attr type_ (Ident ident)) = do
    env <- ask
    case M.lookup cls $ classes env of
        Nothing       -> throwTCM "1IMPOSSIBLE ERROR TODO"
        (Just clsDef) -> do
            -- checkIfMemberExists (members clsDef) ident
            t <- typeToTCType type_
            -- let clsDef' =
            --         clsDef { members = M.insert ident t $ members clsDef }
            let
                env' = env
                    { types = M.insert ident (t, initScope + 1) $ types env
                    } -- TODO: initScope + 1, gurl, zgubisz się (pewnie już się zgubiłaś, ciiiii)
            return env' --{ classes = M.insert cls clsDef' (classes env) }

handleClsMember cls (Meth ret (Ident ident) args _) = ask
    -- do
    -- env <- ask
    -- case M.lookup cls $ classes env of
    --     Nothing       -> throwTCM "2IMPOSSIBLE ERROR TODO"
    --     (Just clsDef) -> do
    --         -- checkIfMemberExists (members clsDef) ident
    --         t <- typeToTCType $ Fun ret (map (\(Arg t _) -> t) args)
    --         -- let clsDef' =
    --                 -- clsDef { members = M.insert ident t $ members clsDef }
    --         return env --{ classes = M.insert cls clsDef' (classes env) }


-- TODO: wywołanie funkcji zewnetrznej w memberze
-- FACT: nie ma rekurencyjnego wywoływania metod TODO: czy musi być?
checkMethods :: Var -> ClMember -> TCM TCEnv
checkMethods cls (  Attr type_ (Ident ident)      ) = ask
checkMethods cls x@(Meth ret (Ident ident) args bs) = do
    env <- ask

    -- TODO: ładne łapanie errorów i dodawanie kontekstu
    case M.lookup cls $ classes env of
        Nothing       -> throwTCM "2IMPOSSIBLE ERROR TODO"
        (Just clsDef) -> case extends clsDef of
            Nothing       -> return ()
            (Just parent) -> case M.lookup parent $ classes env of
                Nothing          -> throwTCM "6IMPOSSIBLE ERROR TODO"
                (Just parentDef) -> case M.lookup ident $ members parentDef of
                    Nothing -> return ()
                    (Just parentMemberType) ->
                        case M.lookup ident $ members clsDef of
                            Nothing -> throwTCM "IMSPOIBLEEEEEEEEE TODO"
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
            { types       = M.insert "self" (TDClass cls, scope env + 1)
                            $       argsTypes
                            `union` types env
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
    t <- checkExprM assignable
    case t of
        (TDClass cls) -> matchParentClasses cls e
        _             -> do
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
    checkIfClassExistsT (Cls ident)
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

-- TODO: czy ma być EQU/NE na obiektach i tablicach? z nullem ma być
checkExprM e@(ERel e1 EQU e2) =
    checkBinOp [TInt, TString, TBool, wildcardClass] e1 e2 >> return TBool
checkExprM e@(ERel e1 NE e2) =
    checkBinOp [TInt, TString, TBool, wildcardClass] e1 e2 >> return TBool

checkExprM e@(ERel e1 _ e2) = checkBinOp [TInt] e1 e2 >> return TBool
checkExprM e@(EAnd e1 e2) = checkBinOp [TBool] e1 e2
checkExprM e@(EOr e1 e2) = checkBinOp [TBool] e1 e2


checkExprM (ENew cls@(Cls (Ident clsName)) ClsNotArr) = do
    checkIfClassExistsT cls
    return $ TDClass clsName
checkExprM (ENew type_ (ArrSize sizeExpr)) = do
    checkIfClassExistsT type_ -- doesn't have to be a class, that's ok
    matchExpType TInt sizeExpr
    TArr <$> typeToTCType type_
checkExprM e@(ENew _ _) = throwMsg ["Illegal `new` expression: ", printTree e]
-- TODO: jak się odwołuję poza tablicę, ale to raczej już później, bo w typechecku chyba nie mogę?
checkExprM (EArrAcc expr1 expr2) = do
    (TArr act) <- matchExpType undefinedArrType expr1
    matchExpType TInt expr2
    return act
checkExprM (EAttrAcc expr (Ident ident))
    | ident == "length" = do
        type_ <- matchExpType undefinedArrType expr
        case type_ of
            -- TODO : .length na tablicy!!!
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
    -- case e1T of
    --     cls@(TDClass clsName) -> do
    --         if wildcardClass `notElem` ts
    --             then throwTCM ""
    --             else matchType [cls] =<< checkExprM e2

    matchType ts e1T
    matchType [e1T] =<< checkExprM e2
    return e1T

  --  msg err = [err, "\nIn:", printTree expr]

--TODO: może tu też trzeba klasy pasowalne ogarniać?
matchType :: [TCType] -> TCType -> TCM ()
matchType [ex] act = when (ex /= act)
    $ throwMsg ["Expected type:", show ex, "\nActual type:", show act]
matchType exs cls@(TDClass _) = when (wildcardClass `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show cls]
matchType exs act = when (act `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show act]
