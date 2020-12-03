module SATypes where

import           AbsLatte


import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trans.Except

import           Data.List                      ( intercalate )
import           Data.Map                      as M
                                                ( Map
                                                , lookup
                                                )
type TCM a = ReaderT TCEnv (ExceptT String IO) a

type Var = String
type Scope = Integer
type Types = M.Map Var (TCType, Scope)

data ClassDef = ClassDef
    { members :: Types -- attributes/methods
    , extends :: Maybe Var
    }  deriving Show

data TCEnv = TCEnv
  { types :: Types
  , classes :: M.Map Var ClassDef
  , scope :: Scope -- current scope
  , expectedRet :: Maybe (TCType, Var) -- expected return type and expecting function name
--   , inLoop :: Bool
  } deriving Show

data TCType = TString | TInt | TBool | TVoid | TArr TCType | TDClass Var | TDFun [TCType] TCType
        deriving Eq

undefinedArrType :: TCType
undefinedArrType = TArr TVoid

instance Show TCType where
    show TString           = "string"
    show TInt              = "int"
    show TBool             = "bool"
    show TVoid             = "void"
    show (TArr    type_  ) = show type_ ++ "[]"
    show (TDClass clsName) = clsName
    show (TDFun args ret ) = "(" ++ show' args ++ ") -> " ++ show ret

show' :: Show a => [a] -> String
show' = intercalate ", " . map show

typeToTCType :: Type -> TCType
typeToTCType Str  = TString
typeToTCType Int  = TInt
typeToTCType Bool = TBool
typeToTCType Void = TVoid
typeToTCType cls@(Cls (Ident clsName)) = -- TODO: check czy to na pewno nic nie psuje
    TDClass clsName
typeToTCType (Arr type_   ) = TArr (typeToTCType type_)
typeToTCType (Fun ret args) = TDFun (map typeToTCType args) (typeToTCType ret)


----------------------------------------------------------------------




checkIfClassExists :: Type -> TCM ()
checkIfClassExists (Cls (Ident var)) = do
    clsDef <- getClassDef var
    case clsDef of
        Nothing -> throwTCM $ "No such class named `" ++ var ++ "` declared"
        _       -> return ()
checkIfClassExists (Arr t) = checkIfClassExists t
checkIfClassExists _       = return ()

getClassDef :: Var -> TCM (Maybe ClassDef)
getClassDef var = do
    env <- asks classes
    return $ M.lookup var env


getVarType :: Var -> TCM TCType
getVarType var = do
    typeScope <- getVarTypeScope var
    case typeScope of
        Nothing       -> throwTCM $ concat ["Variable `", var, "` not declared"]
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
                $  "Variable "
                ++ var
                ++ " already declared"

throwTCM :: String -> TCM a
throwTCM = lift . throwE

throwExtraMsg :: TCM a -> (String -> [String]) -> TCM a
throwExtraMsg act msg = catchError act (throwTCM . unwords . msg)

throwMsg :: [String] -> TCM a
throwMsg = throwTCM . unwords
