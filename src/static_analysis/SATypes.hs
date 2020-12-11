module SATypes where

import           AbsLatte

import           Control.Monad.Reader
import           Control.Monad.Except
import           Control.Monad.Trans.Except

import           Data.List                      ( intercalate )
import           Data.Map                      as M
                                                ( Map
                                                , lookup
                                                )

type Var = String

type Scope = Integer
initScope :: Scope
initScope = 0

type Types = M.Map Var (TCType, Scope)

data ClassDef = ClassDef
    { members :: M.Map Var TCType
    , extends :: Maybe Var
    }  deriving Show

data TCEnv = TCEnv
  { types :: Types
  , classes :: M.Map Var ClassDef
  , scope :: Scope -- current scope
  , expectedRet :: Maybe (TCType, Var) -- expected return type and expecting function/method name
  } deriving Show

type TCM a = ReaderT TCEnv (ExceptT String IO) a


data TCType = TString | TInt | TBool | TVoid | TArr TCType | TDClass Var | TDFun [TCType] TCType
        deriving Eq


wildcardArr :: TCType
wildcardArr = TArr TVoid

wildcardClass :: TCType
wildcardClass = TDClass ""

instance Show TCType where
    show TString           = "string"
    show TInt              = "int"
    show TBool             = "bool"
    show TVoid             = "void"
    show (TArr    type_  ) = show type_ ++ "[]"
    show (TDClass clsName) = "class `" ++ clsName ++ "`"-- TODO: czy wypisywać `class`?
    show (TDFun args ret ) = "(" ++ show' args ++ ") -> " ++ show ret

typeToTCType :: Type -> TCM TCType
typeToTCType Str                       = return TString
typeToTCType Int                       = return TInt
typeToTCType Bool                      = return TBool
typeToTCType Void                      = return TVoid
typeToTCType cls@(Cls (Ident clsName)) = do-- TODO: check czy to na pewno nic nie psuje
    checkIfClassExistsT cls
    return $ TDClass clsName
typeToTCType (Arr type_) = TArr <$> typeToTCType type_
typeToTCType (Fun ret args) =
    TDFun <$> mapM typeToTCType args <*> typeToTCType ret


----------------------------------------------------------------------

matchType :: [TCType] -> TCType -> TCM ()
matchType [TDClass parent] (TDClass cls) = do
    compatibles <- getCompatibleClasses cls
    when (parent `notElem` compatibles) $ throwTCM
        "TODO msg incompatible types (incompatible unrelated classes)"
matchType [ex] act = when (ex /= act)
    $ throwMsg ["expected type:", show ex, "\nactual type  :", show act]
matchType exs cls@(TDClass _) = when (wildcardClass `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show cls]
matchType exs act = when (act `notElem` exs) $ throwMsg
    ["Expected one of types:", show' exs, "\nActual type:", show act]

getCompatibleClasses :: Var -> TCM [Var]
getCompatibleClasses cls = getCompatibles [cls] cls
  where
    getCompatibles :: [Var] -> Var -> TCM [Var]
    getCompatibles compatible cls = do
        p <- getClassParent cls
        case p of
            Nothing       -> return compatible
            (Just parent) -> getCompatibles (parent : compatible) parent



show' :: Show a => [a] -> String
show' = intercalate ", " . map show


checkIfClassExists :: Var -> TCM ()
checkIfClassExists var = do
    clsDef <- getClassDef var
    case clsDef of
        Nothing -> throwTCM $ "No such class named `" ++ var ++ "` declared"
        _       -> return ()

checkIfClassExistsT :: Type -> TCM ()
checkIfClassExistsT (Cls (Ident var)) = checkIfClassExists var
checkIfClassExistsT (Arr t          ) = checkIfClassExistsT t
checkIfClassExistsT _                 = return ()

getClassParent :: Var -> TCM (Maybe Var)
getClassParent cls = do
    checkIfClassExistsT (Cls (Ident cls)) --TODO: UGLY 
    clss <- asks classes
    case M.lookup cls clss of
        Nothing       -> throwTCM "getClassParent:IMPOSSIBLE ERROR TODO"
        (Just clsDef) -> return $ extends clsDef

getClassDef :: Var -> TCM (Maybe ClassDef)
getClassDef var = do
    env <- asks classes
    return $ M.lookup var env

getSureClassDef :: Var -> TCM ClassDef
getSureClassDef cls = do
    classes <- asks classes
    case M.lookup cls $ classes of
        Just clsDef -> return clsDef
        Nothing ->
            throwTCM
                "Impossible - we're checking this class's members, so it was already added to `classes` in env."

getVarType :: Var -> TCM TCType
getVarType var = do
    typeScope <- getVarTypeScope var
    case typeScope of
        Nothing       -> throwTCM $ "Use of undeclared `" ++ var ++ "`"
        (Just (t, _)) -> return t

getVarTypeScope :: Var -> TCM (Maybe (TCType, Scope))
getVarTypeScope var = do
    -- scope <- asks scope
    env <- asks types
    return $ M.lookup var env

checkIfNameAlreadyInScope :: Var -> TCM ()
checkIfNameAlreadyInScope var = do
    scope     <- asks scope
    typeScope <- getVarTypeScope var
    case typeScope of
        Nothing -> return ()
        (Just (_, s)) ->
            when (scope == s)
                $  throwTCM
                $  "`" -- TODO: better message - topdefs fns/classes arent variables
                ++ var
                ++ "` already declared\n"

throwTCM :: String -> TCM a
throwTCM = lift . throwE

throwExtraMsg :: TCM a -> (String -> [String]) -> TCM a
throwExtraMsg act msg = catchError act (throwTCM . unwords . msg)

throwMsg :: [String] -> TCM a
throwMsg = throwTCM . unwords
