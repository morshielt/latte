module ReturnsCheck
    ( checkReturns
    )
where


import           AbsLatte

import           SATypes

import           Control.Monad.Reader
import           Control.Monad.Trans.Except

checkReturns :: [TopDef] -> TCM ()
checkReturns = mapM_ checkTopDefReturn
  where
    checkTopDefReturn :: TopDef -> TCM ()
    checkTopDefReturn (FnDef Void (Ident ident) _ b) = return ()
    checkTopDefReturn (FnDef _    (Ident ident) _ b) = do
        res <- checkReturn (BStmt b)
        if res
            then return ()
            else throwMsg
                ["Missing return value in function: `" ++ ident ++ "`"]
    checkTopDefReturn (ClDef _ _ clsmembers) = mapM_ checkMemberReturns
                                                     clsmembers

      where
        checkMemberReturns :: ClMember -> TCM Bool
        checkMemberReturns (Attr type_ (Ident ident)   ) = return False
        checkMemberReturns (Meth Void (Ident ident) _ b) = return True
        checkMemberReturns (Meth _    (Ident ident) _ b) = do
            res <- checkReturn (BStmt b)
            if res
                then return False
                else throwMsg
                    ["Missing return value in method: 1" ++ ident ++ "`"] -- TODO: in class...

    checkReturn :: Stmt -> TCM Bool
    checkReturn (Ret _)                    = return True
    checkReturn VRet                       = return True
    checkReturn (While ELitTrue s        ) = checkReturn s
    checkReturn (Cond  ELitTrue s        ) = checkReturn s
    checkReturn (CondElse ELitTrue  s1 _ ) = checkReturn s1
    checkReturn (CondElse ELitFalse _  s2) = checkReturn s2
    checkReturn (CondElse _ s1 s2) = (&&) <$> checkReturn s1 <*> checkReturn s2
    checkReturn (BStmt (Block ss)        ) = foldM checkOr False ss
        where checkOr acc s = (||) acc <$> checkReturn s
    checkReturn _ = return False

