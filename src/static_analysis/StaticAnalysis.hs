module StaticAnalysis
    ( runStaticAnalysis
    )
where


import           AbsLatte

import           SATypes
-- import           SAUtils
import           StmtTC                         ( checkStmtM )
import           ReturnsCheck
-- import           PrintLatte (printTree)

import           Control.Monad.Reader


import           Data.List                      ( intercalate )
import           Data.Map                      as M
                                                ( Map
                                                , insert
                                                , fromList
                                                , empty
                                                , lookup
                                                , union
                                                )


-- TODO: posprawdzać jak wyglądają error message

-- TODO: to chyba też już nie w typechecku
-- int[][] arr = new int[][20];
-- arr[1] = 5; -- TODO: co tu w ogóle można przypisać? tablicę odp. długości czy nic czy co????
-- TODO: jak się odwołuję poza tablicę, ale to raczej już później, bo w typechecku chyba nie mogę?
-- TODO: for (int i : arr) i = 5; -- czy to w ogóle se można takie przypisania?
-- TODO: jaki jest default decl klasy rekurencyjnej? (list atrybutem list) null chyba nie?

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
        env  <- ask
        env' <- foldM saveTopDefTypes env prog
        local (const env') checkMainPresent
        env''  <- local (const env') (saveClassesMembers prog)
        env''' <- local (const env'') (checkClassDefsM prog)
        local (const env''') (checkFnDefsM prog)
        checkReturns prog
        ask


checkMainPresent :: TCM ()
checkMainPresent = do
    types <- asks types
    case M.lookup "main" types of
        Nothing -> throwTCM "Missing `main` function declaration"
        (Just (TDFun [] TInt, _)) -> return ()
        (Just (t, _)) -> throwTCM $ "Invalid `main` function type :" ++ show t

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

    checkExtends :: Var -> TCM TCEnv
    checkExtends cls = checkIfExtendsAcyclic [cls] cls

    checkIfExtendsAcyclic :: [Var] -> Var -> TCM TCEnv
    checkIfExtendsAcyclic visited cls = do
        maybeParent <- getClassParent cls
        case maybeParent of
            Nothing       -> ask
            (Just parent) -> if parent `elem` visited
                then
                    throwTCM $ "CYCLIC CLASS EXTENDS TODO msg: " ++ show visited
                else checkIfExtendsAcyclic (parent : visited) parent

    saveClassMembers :: TopDef -> TCM TCEnv
    saveClassMembers FnDef{}                           = ask
    saveClassMembers (ClDef (Ident ident) _ clmembers) = do
        checkExtends ident
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
            Attr type_ (Ident ident) -> saveClassMember' cls ident type_
            Meth ret (Ident ident') args _ ->
                let type_ = Fun ret (map (\(Arg t _) -> t) args)
                in  saveClassMember' cls ident' type_ `throwExtraMsg` msg ident'
          where
            msg ident' e = [e ++ "in method `" ++ ident' ++ "`"]
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
        msg e = [e ++ "in class `" ++ ident ++ "`"]

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
            checkMethods cls Attr{} = ask
            checkMethods cls (Meth ret (Ident ident) args bs) =
                checkMethod `throwExtraMsg` msg'
              where
                msg' e = [e, " in method `", ident, "`"]
                checkMethod = do
                    clsDef <- getSureClassDef cls
                    case extends clsDef of
                        Nothing     -> return ()
                        Just parent -> do
                            parentDef <- getSureClassDef parent
                            matchVirtualMethod clsDef parentDef

                    argsTypes <- handleArgs args
                    let
                        argsTypes' = M.insert selfMember
                                              (TDClass cls, scope env + 1)
                                              argsTypes

                    ret' <- typeToTCType ret
                    env  <- ask
                    let
                        env' = env
                            { types       = argsTypes' `union` types env
                            , expectedRet =
                                Just (ret', " method `" ++ ident ++ "`")
                            }
                    local (const env') $ checkStmtM $ BStmt bs
                    ask
                  where
                    selfMember :: Var
                    selfMember = "self"
                    matchVirtualMethod clsDef parentDef =
                        case M.lookup ident $ members parentDef of
                            Nothing -> return ()
                            Just parentMemberType ->
                                case M.lookup ident $ members clsDef of
                                    Nothing ->
                                        throwTCM
                                            "Impossible - we're currently checking this method's correctness - it has to exist."
                                    Just memberType -> do
                                        matchType [parentMemberType] memberType
                                        return ()

handleArgs :: [Arg] -> TCM Types
handleArgs args = do
    scope <- asks scope
    list  <- mapM
        (\(Arg t (Ident var)) -> do
            t' <- typeToTCType t
            if t' == TVoid
                then
                    throwTCM
                    $  "Illegal `void` type function parameter `"
                    ++ var
                    ++ "`"
                else return (var, (t', scope + 1))
        )
        args
    let mapList = fromList list
    if length list == length mapList
        then return mapList
        else throwTCM "Function arguments must have different names"
    --   where checkVoidParams

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
    where msg e = [e ++ "in function: `" ++ name ++ "`"]
