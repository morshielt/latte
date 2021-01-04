module SAExprs
    ( checkExpr
    , matchExpType
    )
where

import           AbsLatte
import           PrintLatte                     ( printTree )

import           SACommon

import           Control.Monad.Reader           ( asks )
import           Control.Monad                  ( when )
import           Data.Map                      as M
                                                ( lookup )

checkExpr :: Expr -> TCM TCType
checkExpr expr = checkExprM expr `throwExtraMsg` msg expr

checkExprM :: Expr -> TCM TCType
checkExprM (ECastNull ident@(Ident cls)) =
    checkIfClassExistsT (Cls ident) >> return (TDClass cls)
checkExprM (EVar    (Ident var)) = getVarType var

checkExprM (EString _          ) = return TString
checkExprM (ELitInt _          ) = return TInt
checkExprM ELitTrue              = return TBool
checkExprM ELitFalse             = return TBool

checkExprM (  Not e           )  = matchExpType' TBool e
checkExprM (  Neg e           )  = matchExpType' TInt e

checkExprM e@(EMul e1 _     e2)  = checkBinOp [TInt] e1 e2
checkExprM e@(EAdd e1 Plus  e2)  = checkBinOp [TInt, TString] e1 e2
checkExprM e@(EAdd e1 Minus e2)  = checkBinOp [TInt] e1 e2

checkExprM e@(ERel e1 EQU e2) =
    checkBinOp [TInt, TString, TBool, wildcardClass] e1 e2 >> return TBool
checkExprM e@(ERel e1 NE e2) =
    checkBinOp [TInt, TString, TBool, wildcardClass] e1 e2 >> return TBool

checkExprM e@(ERel e1 _ e2) = checkBinOp [TInt, TString] e1 e2 >> return TBool
checkExprM e@(EAnd e1 e2  ) = checkBinOp [TBool] e1 e2
checkExprM e@(EOr  e1 e2  ) = checkBinOp [TBool] e1 e2

checkExprM (ENew (Cls (Ident clsName)) ClsNotArr) =
    checkIfClassExists clsName >> return (TDClass clsName)
checkExprM (ENew type_ (ArrSize sizeExpr)) = do
    checkIfClassExistsT type_
    matchExpType' TInt sizeExpr
    TArr <$> typeToTCType type_
checkExprM e@(ENew    _     _    ) = throwTCM "Illegal `new` expression"
checkExprM (  EArrAcc expr1 expr2) = do
    (TArr act) <- matchExpType' wildcardArr expr1
    matchExpType' TInt expr2
    return act
checkExprM (EAttrAcc expr (Ident ident))
    | ident == "length" = do
        type_ <- matchExpType' wildcardArr expr
        case type_ of
            (TArr _) -> return TInt
            _        -> checkEAttrAcc
    | otherwise = checkEAttrAcc
  where
    checkEAttrAcc = do
        (TDClass clsName) <- matchExpType' wildcardClass expr
        matchAttr clsName
      where
        matchAttr clsName = do
            classes <- asks classes
            case M.lookup clsName classes of
                Nothing ->
                    throwTCM
                        "Impossible, we've found this class by matching so it has to exist"
                (Just clsDef) -> case M.lookup ident (members clsDef) of
                    Nothing -> case extends clsDef of
                        Nothing ->
                            throwTCM $ "No such attribute `" ++ ident ++ "`"
                        Just parent -> matchAttr parent
                    (Just (TDFun _ _)) ->
                        throwTCM
                            $  "`"
                            ++ ident
                            ++ " is a method not an attribute"
                    (Just t) -> return t

checkExprM e@(EMethCall expr (Ident ident) es) = do
    (TDClass clsName) <- matchExpType' wildcardClass expr
    matchMethod clsName
  where
    matchMethod clsName = do
        classes <- asks classes
        case M.lookup clsName classes of
            Nothing ->
                throwTCM
                    "Impossible, we've found this class by matching so it has to exist"
            (Just clsDef) -> case M.lookup ident (members clsDef) of
                Nothing -> case extends clsDef of
                    Nothing     -> throwTCM $ "No such method `" ++ ident ++ "`"
                    Just parent -> matchMethod parent
                (Just (TDFun args ret)) -> do
                    checkArgs args es
                    return ret
                (Just t) ->
                    throwTCM $ "`" ++ ident ++ " is an attribute not a method"

checkExprM (EApp (Ident var) es) = do
    typeScope <- getVarType var
    case typeScope of
        TDFun args ret -> do
            checkArgs args es
            return ret
        _ -> throwTCM $ var ++ " is not a function"

checkArgs :: [TCType] -> [Expr] -> TCM ()
checkArgs args es = if length args == length es
    then mapM_ checkArg $ zip args es
    else throwTCM "Invalid number of arguments in function call"
    where checkArg (t, e) = matchExpType' t e

checkBinOp :: [TCType] -> Expr -> Expr -> TCM TCType
checkBinOp ts e1 e2 = do
    e1T <- checkExprM e1
    e2T <- checkExprM e2
    case (e1T, e2T) of
        (TDClass e1C, TDClass e2C) -> checkAnyClassCompatibility e1C e2C
        _                          -> do
            matchType ts    e1T
            matchType [e1T] e2T
    return e1T
  where
    checkAnyClassCompatibility :: Var -> Var -> TCM ()
    checkAnyClassCompatibility cls1 cls2 = do
        compatibles1 <- getCompatibleClasses cls1
        when (cls2 `notElem` compatibles1) $ do
            compatibles2 <- getCompatibleClasses cls2
            when (cls1 `notElem` compatibles2)
                $  throwTCM
                $  "Incompatible types "
                ++ cls1
                ++ " and "
                ++ cls2

matchExpType :: TCType -> Expr -> TCM TCType
matchExpType ex e = matchExpType' ex e `throwExtraMsg` msg e

matchExpType' :: TCType -> Expr -> TCM TCType
matchExpType' ex e
    | ex == wildcardArr = do
        act <- checkExprM e
        case act of
            (TArr type_) -> return act
            _ ->
                throwTCM
                    $  "expected type : any array type\nactual type:"
                    ++ show act
        return act
    | ex == wildcardClass = do
        act <- checkExprM e
        case act of
            (TDClass clsName) -> return act
            _ ->
                throwTCM
                    $  "expected type: any class type\nactual type:"
                    ++ show act

        return act
    | otherwise = do
        act <- checkExprM e
        matchType [ex] act
        return act

msg expr e = e ++ "\nin expression: " ++ printTree expr ++ "\n"
