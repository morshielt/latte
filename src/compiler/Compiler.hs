module Compiler
    ( compile
    )
where

import           AbsLatte

import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Trans.Except
import           Data.Map                      as M
                                                ( Map
                                                , empty
                                                , lookup
                                                , insert
                                                )


type Var = String
type Register = Integer
type Store = M.Map Var Register

data CEnv = CEnv
  { varToRegister :: Store
  , freeLabel :: Integer  } deriving Show

type CM a = StateT CEnv (ExceptT String IO) a


-- type Label = String
-- type Ins = ShowS
-- data Instrs = IB Label [Ins] Ins

throwCM :: String -> CM a
throwCM = lift . throwE

compile (Program prog) = evalStateT (go prog) $ CEnv M.empty 0
    where go prog = flip ($) "" <$> genExpr prog

genExpr :: [TopDef] -> CM ShowS
genExpr = foldM go x86Intro
  where
    go accCode stmt = do
        code <- transTopDef stmt
        return (accCode . code)

transTopDef :: TopDef -> CM ShowS
transTopDef x = case x of
    FnDef ret (Ident name) args (Block ss) -> do
        code <- foldM go (showString "") ss
        return $ label name . prelude . code
    ClDef{} -> throwCM "classes not implemented yet"
  where
    go :: ShowS -> Stmt -> CM ShowS
    go accCode stmt = do
        code <- transStmt stmt
        return (accCode . code)


transStmt :: Stmt -> CM ShowS
transStmt x = case x of
    Empty -> return id
    VRet  -> return ret
    Ret e -> do
        code <- transExpr e
        return $ code . ret
    SExp e   -> transExpr e
    Cond e s -> do
        condCode   <- transExpr e
        trueCode   <- transStmt s
        afterLabel <- getFreeLabel
        let op =
                pop eax . binIns "cmp" (lit trueLit) eax . unIns "je" afterLabel
        return $ condCode . op . trueCode . label afterLabel
    x -> throwCM $ show x ++ "\nstmt not implemented yet"

transExpr :: Expr -> CM ShowS
transExpr (ELitInt n) = return $ push $ lit n
transExpr ELitTrue    = return $ push $ lit trueLit
transExpr ELitFalse   = return $ push $ lit 0
transExpr (Neg e)     = do
    code <- transExpr e
    return $ code . neg
  where
    neg :: ShowS
    neg = pop eax . unIns "neg" eax . push eax

transExpr (EAdd e1 op e2) = do
    let op' = case op of
            Plus  -> "add"
            Minus -> "sub"
    transBinOp e1 e2 $ binOp (binIns op' ebx eax) eax
transExpr (EMul e1 Times e2) =
    transBinOp e1 e2 $ binOp (binIns "imul" ebx eax) eax
transExpr (EMul e1 op e2) = do
    let ret = case op of
            Div -> eax
            Mod -> edx
    transBinOp e1 e2 $ binOp (zIns "cdq" . binIns "idiv" ebx eax) ret

transExpr e@(ERel e1 op e2) = do -- TODO: UNCHECKED
    code1      <- transExpr e1
    code2      <- transExpr e2
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel
    let ops =
            pop ebx
                . pop eax
                . binIns "cmp" ebx eax
                . unIns (chooseOp op) trueLabel
                . push (lit falseLit)
                . unIns "jmp" afterLabel
                . label trueLabel
                . push (lit trueLit)
                . label afterLabel

    return $ code1 . code2 . ops
  where
    chooseOp op = case op of
        LTH -> "jl"
        LE  -> "jle"
        GTH -> "jg"
        GE  -> "jge"
        EQU -> "je"
        NE  -> "jne"

transExpr (EApp (Ident var) es) = do
    es' <- mapM transExpr es
    let ess = foldr (.) id (reverse es')
    return $ ess . unIns "call" var


getFreeLabel :: CM String
getFreeLabel = do
    label <- gets freeLabel
    modify (\st -> st { freeLabel = label + 1 })
    return $ ".label" ++ show label

transBinOp :: Expr -> Expr -> ShowS -> CM ShowS
transBinOp e1 e2 opCode = do
    code1 <- transExpr e1
    code2 <- transExpr e2
    return $ code1 . code2 . opCode


x86Intro = showString ".text\n.globl main\n\n"

label l = showString $ l ++ ":\n"
prelude = push ebp . showInd "mov %esp, %ebp\n"

mov :: String -> String -> ShowS
mov = binIns "mov"

pop, push :: String -> ShowS
pop = unIns "pop"
push = unIns "push"

ret :: ShowS
ret = pop eax . mov ebp esp . pop ebp . zIns "ret"


binOp ops ret = pop ebx . pop eax . ops . push ret -- TODO: jak są stałe, to teoretycznie nie trzebaby ich push/pop tylko wpisać żywcem D:

zIns instr = showInd $ instr ++ "\n"
unIns instr cont = showInd $ instr ++ " " ++ cont ++ "\n"
binIns instr cont1 cont2 =
    showInd $ instr ++ " " ++ cont1 ++ ", " ++ cont2 ++ "\n"

showInd s = showString "    " . showString s

lit :: Integer -> String
lit n = '$' : show n

eax, ebx, ebp, esp :: String
eax = "%eax"
ebx = "%ebx"
edx = "%edx"
ebp = "%ebp"
esp = "%esp"

trueLit = 1
falseLit = 0
