module Compiler
    ( compile
    , x86
    )
where

import           AbsLatte


import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Trans.Except
import           Data.Bits                      ( (.&.) )
import           Data.Map                      as M
                                                ( Map
                                                , empty
                                                , lookup
                                                , insert
                                                )


type Var = String
type Offset = Integer
-- type Label = Integer
type Scope = Integer
type VOS = M.Map (Var, Scope) Offset

data CEnv = CEnv
  {
    scope :: Scope
    -- , stack :: Integer
  } --deriving Show

data CState = CState
  { freeLabel :: Integer
  , locals :: Integer
  , stack :: Integer
  , maxStack :: Integer
  , maxArgs :: Integer
  , retLabel :: String
  , varOffScope :: VOS
  } --deriving Show

-- type CMonad a = RWS CEnv AsmStmts CState a

type CM a = ReaderT CEnv (StateT CState (ExceptT String IO)) a

throwCM :: String -> CM a
throwCM = lift . lift . throwE

compile (Program prog) = evalStateT (runReaderT (go prog) (CEnv 0))
                                    (CState 0 0 0 0 0 "" M.empty)
    where go prog = flip ($) [] <$> genExpr prog >>= x86

genExpr :: [TopDef] -> CM InstrS
genExpr = foldM go $ instrS Intro
  where
    go accCode stmt = do
        code <- transTopDef stmt
        return (accCode . code)

transTopDef :: TopDef -> CM InstrS
transTopDef x = case x of
    FnDef ret (Ident name) args (Block ss) -> do
        modify
            (\st -> st { locals      = 0
                       , varOffScope = M.empty
                       , retLabel    = "ret_" ++ name
                       }
            )
        --TODO: dodać se argumenty do varOffScope XD
        code   <- transStmts ss
        vars   <- countVars ss
        retLab <- gets retLabel
        return
            $ instrSS [Lab $ FuncLabel name, Prologue, StackAlloc vars]
            . code
            . instrSS [Lab $ FuncLabel retLab, Epilogue, ZIns RET]
    ClDef{} -> throwCM "classes not implemented yet"

transStmts :: [Stmt] -> CM InstrS
transStmts = foldM go id
  where
    go :: InstrS -> Stmt -> CM InstrS
    go accCode stmt = do
        code <- transStmt stmt
        return (accCode . code)

countVars :: [Stmt] -> CM Integer
countVars []       = return 0
countVars (s : ss) = do
    sVars <- case s of
        Decl _ ds          -> return $ fromIntegral $ length ds
        BStmt (Block bs)   -> countVars bs
        Cond _ bs          -> countVars [bs]
        CondElse _ bs1 bs2 -> (+) <$> countVars [bs1] <*> countVars [bs2]
        While _ bs         -> countVars [bs]
        For _ _ _ bs       -> (+ 1) <$> countVars [bs] -- TODO: dodać tę zmienną iteracyjną do scope+1 ręcznie
        _                  -> return 0
    ssVars <- countVars ss
    return $ sVars + ssVars

transStmt :: Stmt -> CM InstrS
transStmt x = case x of
    Empty -> return id
    VRet  -> instrS . Jump JMP . FuncLabel <$> gets retLabel
    Ret e -> do
        code   <- transExpr e
        retLab <- gets retLabel
        return $ code . instrSS [POP $ Reg EAX, Jump JMP $ FuncLabel retLab]
    SExp e   -> transExpr e
    Cond e s -> do
        condCode   <- transExpr e
        trueCode   <- transAsBStmt s
        afterLabel <- getFreeLabel
        let op =
                instrSS
                        [ POP $ Reg EAX
                        , BinIns CMP falseLit $ Reg EAX
                        , Jump JE $ JmpLabel afterLabel
                        ]
                    . trueCode
                    . instrS (Lab $ JmpLabel afterLabel)
        return $ condCode . op
    CondElse e s1 s2 -> do
        condCode   <- transExpr e
        trueCode   <- transAsBStmt s1
        falseCode  <- transAsBStmt s2
        falseLabel <- getFreeLabel
        afterLabel <- getFreeLabel
        let op =
                instrSS
                        [ POP $ Reg EAX
                        , BinIns CMP falseLit $ Reg EAX
                        , Jump JE $ JmpLabel falseLabel
                        ]
                    . trueCode
                    . instrS (Jump JE $ JmpLabel afterLabel)
                    . instrS (Lab $ JmpLabel falseLabel)
                    . falseCode
                    . instrS (Lab $ JmpLabel afterLabel)
        return $ condCode . op
    While e s -> do
        condCode  <- transExpr e
        loopCode  <- transAsBStmt s
        condLabel <- getFreeLabel
        loopLabel <- getFreeLabel
        return
            $ instrS (Jump JMP $ JmpLabel condLabel)
            . instrS (Lab $ JmpLabel loopLabel)
            . loopCode
            . instrS (Lab $ JmpLabel condLabel)
            . instrSS
                  [ POP $ Reg EAX
                  , BinIns CMP trueLit $ Reg EAX
                  , Jump JE $ JmpLabel loopLabel
                  ]
    Decl _   ds -> foldr (.) id <$> mapM handleDecl ds
    Ass  ass e  -> do
        exprCode <- transExpr e
        (mem, _) <- transAssignable ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        return $ exprCode . instrSS [POP $ Reg EAX, MOV (Reg EAX) $ Mem mem]
    Incr ass -> do
        (mem, _) <- transAssignable ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        return $ instrSS [UnIns INC $ Mem mem]
    Decr ass -> do
        (mem, _) <- transAssignable ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        return $ instrSS [UnIns DEC $ Mem mem]
    BStmt (Block bs) ->
        local (\env -> env { scope = scope env + 1 }) $ transStmts bs

    x -> throwCM $ show x ++ "\nstmt not implemented yet"
  where
    transAsBStmt :: Stmt -> CM InstrS
    transAsBStmt s@(BStmt _) = transStmt s
    transAsBStmt s           = transStmt (BStmt (Block [s]))
    handleDecl :: Item -> CM InstrS
    handleDecl d = do
        state <- get
        sco   <- asks scope
        let loc = locals state + 1
        case d of
            (NoInit (Ident var)) -> do
                modify
                    (\st -> st
                        { varOffScope = M.insert (var, sco) loc
                                            $ varOffScope state
                        , locals      = loc
                        }
                    )
                return id
            (Init (Ident var) e) -> do
                modify
                    (\st -> st
                        { varOffScope = M.insert (var, sco) loc
                                            $ varOffScope state
                        , locals      = loc
                        }
                    )
                initCode <- transExpr e
                return $ initCode . instrSS
                    [POP $ Reg EAX, MOV (Reg EAX) (Mem $ Local loc)]

transAssignable :: Expr -> CM (Memory, InstrS)
transAssignable (EVar (Ident var)) = do
    sco <- asks scope
    loc <- findInAnyScope var sco
    return (Local loc, id)
-- TODO: tablice/pole ogarnąć instrukcje kolejność no
transAssignable _ = throwCM "Not an assignable or not implemented"

findInAnyScope :: Var -> Scope -> CM Offset
findInAnyScope var (-1) = throwCM "Impossible findInAnyScope"
findInAnyScope var sco  = do
    state <- get
    case M.lookup (var, sco) (varOffScope state) of
        Nothing  -> findInAnyScope var $ sco - 1
        Just loc -> return loc

transExpr :: Expr -> CM InstrS
transExpr (EVar (Ident var)) = do
    sco <- asks scope
    loc <- findInAnyScope var sco
    return $ instrS $ PUSH $ Mem $ Local loc

transExpr (ELitInt n) = return $ instrS $ PUSH (Lit n)
transExpr ELitTrue    = return (PUSH trueLit :)
transExpr ELitFalse   = return (PUSH falseLit :)
transExpr (Neg e)     = do
    code <- transExpr e
    return $ code . neg
  where
    neg :: InstrS
    neg = instrSS [POP $ Reg EAX, UnIns NEG $ Reg EAX, PUSH $ Reg EAX]

transExpr (Not e) = do
    code <- transExpr e
    return $ code . not
  where
    not :: InstrS
    not = instrSS [POP $ Reg EAX, BinIns XOR (Lit 1) $ Reg EAX, PUSH $ Reg EAX]

transExpr (EAdd e1 op e2) = do
    let op' = case op of
            Plus  -> ADD -- TODO: STRINGI!
            Minus -> SUB
    transBinOp e1 e2 $ binOp [BinIns op' (Reg ECX) $ Reg EAX] $ Reg EAX
transExpr (EMul e1 Times e2) =
    transBinOp e1 e2 $ binOp [BinIns MUL (Reg ECX) $ Reg EAX] $ Reg EAX
transExpr (EMul e1 op e2) = do
    let ret = case op of
            Div -> Reg EAX
            Mod -> Reg EDX
    transBinOp e1 e2 $ binOp [ZIns CDQ, BinIns DIV (Reg ECX) $ Reg EAX] ret

transExpr e@(ERel e1 op e2) = do -- TODO: UNCHECKED
    code1      <- transExpr e1
    code2      <- transExpr e2
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel
    let ops =
            [ POP $ Reg ECX
            , POP $ Reg EAX
            , BinIns CMP (Reg ECX) $ Reg EAX
            , Jump (chooseOp op) $ JmpLabel trueLabel
            , PUSH falseLit
            , Jump JMP $ JmpLabel afterLabel
            , Lab $ JmpLabel trueLabel
            , PUSH trueLit
            , Lab $ JmpLabel afterLabel
            -- , label trueLabel
            -- , push trueLit
            -- , label afterLabel
            ]

    return $ code1 . code2 . instrSS ops
  where
    chooseOp op = case op of
        LTH -> JL
        LE  -> JLE
        GTH -> JG
        GE  -> JGE
        EQU -> JE -- TODO: STRINGI!
        NE  -> JNE

transExpr (EApp (Ident var) es) = do
    es' <- mapM transExpr es
    let ess = foldr (.) id (reverse es')
    return $ ess . instrS (CALL var $ fromIntegral $ length es)

transExpr (EAnd e1 e2) = do
    falseLabel <- getFreeLabel
    afterLabel <- getFreeLabel

    code1      <- transExpr e1
    let shortCirc = instrSS
            [ POP $ Reg EAX
            , BinIns CMP falseLit $ Reg EAX
            , Jump JE $ JmpLabel falseLabel
            ]
    code2 <- transExpr e2
    let trueCode = instrSS [PUSH trueLit, Jump JMP $ JmpLabel afterLabel]
    let outro =
            instrSS
                [ Lab $ JmpLabel falseLabel
                , PUSH falseLit
                , Lab $ JmpLabel afterLabel
                ]
    return $ code1 . shortCirc . code2 . shortCirc . trueCode . outro

transExpr (EOr e1 e2) = do
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel

    code1      <- transExpr e1
    let shortCirc = instrSS
            [ POP $ Reg EAX
            , BinIns CMP trueLit $ Reg EAX
            , Jump JE $ JmpLabel trueLabel
            ]
    code2 <- transExpr e2
    let falseCode = instrSS [PUSH falseLit, Jump JMP $ JmpLabel afterLabel]
    let outro =
            instrSS
                [ Lab $ JmpLabel trueLabel
                , PUSH trueLit
                , Lab $ JmpLabel afterLabel
                ]
    return $ code1 . shortCirc . code2 . shortCirc . falseCode . outro
-- if w1 goto Ltrueif w2 goto Ltrue
    -- code for Lfalse or goto Lfalse


transExpr e = throwCM $ show e

-- TODO: jak są stałe, to teoretycznie nie trzebaby ich push/pop tylko wpisać żywcem D: jebać
binOp ops ret = instrSS $ [POP $ Reg ECX, POP $ Reg EAX] ++ ops ++ [PUSH ret]

getFreeLabel :: CM Integer
getFreeLabel = do
    label <- gets freeLabel
    modify (\st -> st { freeLabel = label + 1 })
    return label

transBinOp :: Expr -> Expr -> InstrS -> CM InstrS
transBinOp e1 e2 opCode = do
    code1 <- transExpr e1
    code2 <- transExpr e2
    return $ code1 . code2 . opCode

trueLit = Lit 1
falseLit = Lit 0

data Register = EAX | ECX | EDX | EBP | ESP -- deriving Eq
instance Show Register where
    show EBP = "%ebp"
    show ESP = "%esp"
    show EAX = "%eax"
--   show EBX = "%ebx"
    show EDX = "%edx"
    show ECX = "%ecx"
--   show EDI = "%edi"
--   show ESI = "%esi"

data Memory = Local Integer | Param Integer | Stack Integer
instance Show Memory where
    show (Param n) = show (dword * n) ++ "(" ++ show EBP ++ ")" -- TODO: jeszcze jakoś +/- 4 bo ten adr powr czy co to tam jest czy nie?
    show (Local n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"
    show (Stack n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"

data Operand = Reg Register | Mem Memory | Lit Integer
instance Show Operand where
    show (Reg r) = show r
    show (Mem m) = show m
    show (Lit l) = '$' : show l

data JOp = JL | JLE | JG | JGE | JE | JNE | JMP deriving Show
data BinOp = ADD | SUB | MUL | DIV | XOR | CMP -- deriving Show -- deriving Eq  --  SAL
instance Show BinOp where
    show ADD = "addl "
    show SUB = "subl "
    show DIV = "idiv "
    show MUL = "imul "
    show XOR = "xor "
    show CMP = "cmp "

data UnOp = NEG | INC | DEC
instance Show UnOp where
    show NEG = "neg "
    show INC = "incl "
    show DEC = "decl "

data ZOp = RET | CDQ deriving Show

data Label = FuncLabel String | JmpLabel Integer -- | BranchLabel Integer
instance Show Label where
    show (FuncLabel f) = f
    show (JmpLabel  i) = ".L" ++ show i

data Instr = Intro
    | Prologue
    | StackAlloc Integer
    | Epilogue
    | CALL String Integer
    | MOV Operand Operand
    | PUSH Operand
    | POP Operand
    | ARGPUSH Operand
    | Jump JOp Label
    | ZIns ZOp
    | UnIns UnOp Operand
    | BinIns BinOp Operand Operand
    | Lab Label
instance Show Instr where
    show Intro = ".text\n.globl main\n"
    show Prologue =
        show (PUSH $ Reg EBP) ++ "\n" ++ show (MOV (Reg ESP) $ Reg EBP)
    show (StackAlloc n) = show $ BinIns SUB (Lit (dword * n)) $ Reg ESP --TODO: align 16
    show Epilogue =
        show (MOV (Reg EBP) $ Reg ESP) ++ "\n" ++ show (POP $ Reg EBP)
    show (CALL l _       ) = "call " ++ l
    show (MOV  o r       ) = "movl " ++ show o ++ ", " ++ show r
    show (PUSH op        ) = "pushl " ++ show op
    show (POP  op        ) = "popl " ++ show op
    show (ZIns zin       ) = show zin
    show (UnIns unop unin) = show unop ++ " " ++ show unin
    show (Jump  unop unin) = show unop ++ " " ++ show unin
    show (BinIns bop bin1 bin2) =
        show bop ++ " " ++ show bin1 ++ ", " ++ show bin2
    show (Lab l) = show l ++ ":"

dword = 4

type InstrS = [Instr] -> [Instr]
instrSS :: [Instr] -> InstrS
instrSS = (++)
instrS :: Instr -> InstrS
instrS = (:)

x86 :: [Instr] -> CM String
x86 ins = return $ (unlines . map show) ins

-- TODO: stack align 16 jeśli trzeba
