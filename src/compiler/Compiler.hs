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
                                                , size
                                                , elems
                                                , fromList
                                                )
--TODO: spr w typecheck czy ktoś nie deklaruje klasy 'bool' 'int' czy coś XDDD

type Var = String
type Offset = Integer
-- type Label = Integer
type Scope = Integer
type VM = M.Map Var (Memory, Type)

data CEnv = CEnv
  {
    scope :: Scope
  , varMem :: VM
    -- , stack :: Integer
  } --deriving Show

data CState = CState
  { freeLabel :: Integer
  , locals :: Integer
  , stack :: Integer
  , maxStack :: Integer
  , maxArgs :: Integer
  , retLabel :: String
  , strings :: M.Map String Label
  , funRet :: M.Map Var Type
--   , ins :: InstrS
  } --deriving Show

-- type CMonad a = RWS CEnv AsmStmts CState a

type CM a = ReaderT CEnv (StateT CState (ExceptT String IO)) a

throwCM :: String -> CM a
throwCM = lift . lift . throwE

compile (Program prog) = evalStateT
    (runReaderT (go prog) (CEnv 0 M.empty))
    (CState 0 0 0 0 0 "" M.empty predefinedFns)
  where
    go prog = flip ($) [] <$> genExpr prog >>= x86
    predefinedFns :: M.Map Var Type
    predefinedFns = M.fromList
        [ ("printInt"     , Void)
        , ("printString"  , Void)
        , ("error"        , Void)
        , ("readInt"      , Int)
        , ("readString"   , Str)
        , ("concatStrings", Str) --TODO: nazwa lepsza czy coś
        ]



genExpr :: [TopDef] -> CM InstrS
genExpr tds = do
    code <- foldM go id tds
    strs <- gets strings
    let strLabels = map Lab $ M.elems strs
    return $ instrS Intro . instrSS strLabels . code

  where
    go accCode stmt = do
        code <- transTopDef stmt
        return (accCode . code)

transTopDef :: TopDef -> CM InstrS
transTopDef x = case x of
    FnDef ret (Ident name) args b -> do
        modify
            (\st -> st { locals   = 0
                       , retLabel = "ret_" ++ name
                       , funRet   = M.insert name ret $ funRet st
                       }
            )
        --TODO: dodać se argumenty do varMem XD
        (_, code) <- local
            (\env -> env
                { varMem = M.fromList $ zipWith
                               (\(Arg t (Ident var)) i -> (var, (Param i, t)))
                               args
                               [1 ..] -- TODO: od 1 czy od 0?}) 
                }
            )
            (transStmt (BStmt b))
        -- vars   <- countVars ss
        state <- get
        return
            $ instrSS
                  [Lab $ FuncLabel name, Prologue, StackAlloc $ locals state]
            . code
            . instrSS [Lab $ FuncLabel $ retLabel state, Epilogue, ZIns RET]
    ClDef{} -> throwCM "classes not implemented yet"

transStmt :: Stmt -> CM (CEnv, InstrS)
transStmt x = case x of
    Empty -> do
        env <- ask
        return (env, id)
    VRet -> do
        env <- ask
        lab <- gets retLabel
        return (env, instrS $ Jump JMP $ FuncLabel lab)
    Ret e -> do
        code <- transExpr e
        env  <- ask
        lab  <- gets retLabel
        return (env, code . instrSS [POP $ Reg EAX, Jump JMP $ FuncLabel lab])
    SExp e -> do
        code <- transExpr e
        env  <- ask
        return (env, code)

    Cond e s -> do
        condCode   <- transExpr e
        trueCode   <- transAsBStmt s --TODO: czy mam porzucić ten env?
        afterLabel <- getFreeLabel
        let op =
                instrSS
                        [ POP $ Reg EAX
                        , BinIns CMP falseLit $ Reg EAX
                        , Jump JE $ JmpLabel afterLabel
                        ]
                    . trueCode
                    . instrS (Lab $ JmpLabel afterLabel)
        env <- ask
        return (env, condCode . op)
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
                    . instrS (Jump JMP $ JmpLabel afterLabel)
                    . instrS (Lab $ JmpLabel falseLabel)
                    . falseCode
                    . instrS (Lab $ JmpLabel afterLabel)
        env <- ask
        return (env, condCode . op)
    While e s -> do
        condCode  <- transExpr e
        loopCode  <- transAsBStmt s
        condLabel <- getFreeLabel
        loopLabel <- getFreeLabel
        env       <- ask
        return
            ( env
            , instrS (Jump JMP $ JmpLabel condLabel)
            . instrS (Lab $ JmpLabel loopLabel)
            . loopCode
            . instrS (Lab $ JmpLabel condLabel)
            . condCode
            . instrSS
                  [ POP $ Reg EAX
                  , BinIns CMP trueLit $ Reg EAX
                  , Jump JE $ JmpLabel loopLabel
                  ]
            )
    Decl t ds -> if t `notElem` [Int, Bool, Str]
        then throwCM $ "Decl for " ++ show t ++ " not impl yet"
        else do
            env <- ask
            foldM (goDecl t) (env, id) ds

    Ass ass e -> do
        exprCode <- transExpr e
        (mem, _) <- transAssignable ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env      <- ask
        return
            (env, exprCode . instrSS [POP $ Reg EAX, MOV (Reg EAX) $ Mem mem])
    Incr ass -> do
        (mem, _) <- transAssignable ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env      <- ask
        return (env, instrSS [UnIns INC $ Mem mem])
    Decr ass -> do
        (mem, _) <- transAssignable ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env      <- ask
        return (env, instrSS [UnIns DEC $ Mem mem])
    BStmt (Block ss) -> do
        env <- ask
        local (\env -> env { scope = scope env + 1 }) $ transStmts ss
    x -> throwCM $ show x ++ "\nstmt not implemented yet"
  where
    transStmts :: [Stmt] -> CM (CEnv, InstrS)
    transStmts ss = do
        env       <- ask
        (_, code) <- foldM go (env, id) ss
        return (env, code)
      where
        go :: (CEnv, InstrS) -> Stmt -> CM (CEnv, InstrS)
        go (env', accCode) s = do
            (env'', code) <- local (const env') $ transStmt s
            return (env'', accCode . code)
    transAsBStmt :: Stmt -> CM InstrS --TODO: czy mam tu porzucać env? 
    transAsBStmt s@(BStmt _) = do
        (_, code) <- transStmt s
        return code
    transAsBStmt s = do
        (_, code) <- transStmt (BStmt (Block [s]))
        return code
    goDecl :: Type -> (CEnv, InstrS) -> Item -> CM (CEnv, InstrS)
    goDecl t (env', accCode) d = do
        -- t'            <- typeToTCType t
        (env'', code) <- local (const env') $ handleDecl t d
        return (env'', accCode . code)
    -- handleDecl :: TCType -> Item -> TCM TCEnv
    handleDecl :: Type -> Item -> CM (CEnv, InstrS)
    handleDecl t d = do
        state <- get
        sco   <- asks scope
        let loc = Local $ locals state + 1
        modify (\st -> st { locals = locals state + 1 })
        (var, code) <- case d of
            (NoInit (Ident var)) -> do
                def <- defaultValue t
                return (var, instrS $ MOV def (Mem loc)) -- TODO: inicjalizacja domyślna!
            (Init (Ident var) e) -> do
                initCode <- transExpr e
                return
                    ( var
                    , initCode
                        . instrSS [POP $ Reg EAX, MOV (Reg EAX) (Mem loc)]
                    )
        env <- ask
        let envWithDecl = M.insert var (loc, t) $ varMem env
        return (env { varMem = envWithDecl }, code)
      where
        defaultValue :: Type -> CM Operand
        defaultValue Int  = return $ Lit 0
        defaultValue Bool = return falseLit
        defaultValue Str  = StrLit <$> getStrLabel ""
        defaultValue x =
            throwCM $ "defaultValue for " ++ show x ++ " not impl yet"

transAssignable :: Expr -> CM (Memory, InstrS)
transAssignable (EVar (Ident var)) = do
    env <- ask
    case M.lookup var (varMem env) of
        Nothing       -> throwCM "Impossible transExpr (EVar (Ident var))"
        Just (loc, _) -> return (loc, id)
-- TODO: tablice/pole ogarnąć instrukcje kolejność no
transAssignable _ = throwCM "Not an assignable or not implemented"

-- findInAnyScope :: Var -> Scope -> CM Memory
-- findInAnyScope var (-1) = throwCM "Impossible findInAnyScope"
-- findInAnyScope var sco  = do
--     state <- get
--     case M.lookup (var, sco) (varMem state) of
--         Nothing  -> findInAnyScope var $ sco - 1
--         Just loc -> return loc

--TODO: return expr w eax i wtedy push tylko jak złożony i potem brać bez popa tylko od razu z eax ogar.

getStrLabel :: String -> CM Integer
getStrLabel str = do
    strs <- gets strings
    case M.lookup str strs of
        Nothing -> do
            let i = fromIntegral $ M.size strs
            modify (\st -> st { strings = M.insert str (StrLabel i str) strs })
            return i
        Just (StrLabel i str) -> return i

transExpr :: Expr -> CM InstrS
transExpr (EString str) = do
    index <- getStrLabel str
    return $ instrS $ PUSH $ StrLit index

transExpr (EVar (Ident var)) = do
    -- sco <- asks scope
    -- loc <- findInAnyScope var sco
    env <- ask
    case M.lookup var (varMem env) of
        Nothing       -> throwCM "Impossible transExpr (EVar (Ident var))"
        Just (loc, _) -> return $ instrS $ PUSH $ Mem loc

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
    t <- getExprType e1
    case t of
        Str -> transExpr (EApp (Ident "concatStrings") [e1, e2])
            -- do
            -- code1 <- transExpr e1
            -- code2 <- transExpr e2
            -- let strConcat = instrSS [CALL "concatStrings" 2, PUSH $ Reg EAX]
            -- return $ code2 . code1 . strConcat
        _   -> do
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
    return $ ess . instrSS
        [ CALL var $ fromIntegral $ length es
        , BinIns ADD (Lit (dword * fromIntegral (length es))) $ Reg ESP
        , PUSH $ Reg EAX
        ]

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

getExprType :: Expr -> CM Type
getExprType (EVar (Ident var)) = do
    env <- ask
    case M.lookup var (varMem env) of
        Nothing     -> throwCM "Impossible getExprType (EVar (Ident var))"
        Just (_, t) -> return t

getExprType (ELitInt _)            = return Int

getExprType ELitTrue               = return Bool

getExprType ELitFalse              = return Bool

-- getExprType (ENewCls t@(ClsType ident)) = return t

-- getExprType (ENewArr t     _          ) = return (ArrType t)

getExprType (EApp (Ident ident) _) = do
    state <- get
    case M.lookup ident (funRet state) of
        Nothing -> throwCM "Impossible getExprType (EVar (Ident var))"
        Just t  -> return t

-- getExprType (EPropApp expr ident _    ) = do
--     (ClsType t) <- getExprType expr
--     clt         <- getClassType t
--     return $ retType $ case M.lookup ident (fenv clt) of
--         (Just x) -> x
--         Nothing  -> error "Fun in cls fenv lookup!"
-- getExprType (EProp expr ident) = do
--     t <- getExprType expr
--     case t of
--         (ClsType name) -> do
--             clt <- getClassType name
--             return $ vtype $ case M.lookup ident (venv clt) of
--                 (Just x) -> x
--                 Nothing  -> error "EProp lookup in getExprType (EProp ...)"
--         (ArrType _) -> return Int  -- The only property is "length", already checked by StaticChecker
-- getExprType (EArrGet e _) = do
--     (ArrType t) <- getExprType e
--     return t
-- getExprType (ENullCast ident) = return $ ClsType ident
getExprType (EString _)      = return Str
getExprType (Neg     _)      = return Int
getExprType (Not     _)      = return Bool
getExprType EMul{}           = return Int
getExprType (EAdd e Plus  _) = getExprType e
getExprType (EAdd e Minus _) = return Int
getExprType ERel{}           = return Bool
getExprType EAnd{}           = return Bool
getExprType EOr{}            = return Bool

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
    show (Param n) = show (dword * (n + 1)) ++ "(" ++ show EBP ++ ")" -- TODO: jeszcze jakoś +/- 4 bo ten adr powr czy co to tam jest czy nie?
    show (Local n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"
    show (Stack n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"

data Operand = Reg Register | Mem Memory | Lit Integer | StrLit Integer
instance Show Operand where
    show (Reg    r) = show r
    show (Mem    m) = show m
    show (Lit    l) = '$' : show l
    show (StrLit i) = '$' : show (StrLabel i "")

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

data Label = FuncLabel String | JmpLabel Integer  | StrLabel Integer String
instance Show Label where
    show (FuncLabel f ) = f
    show (JmpLabel  i ) = ".L" ++ show i
    show (StrLabel i _) = ".LC" ++ show i

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
    show (Lab l@(StrLabel _i s)) = show l ++ ":\n    .string " ++ show s
    show (Lab l                ) = show l ++ ":"

dword = 4

type InstrS = [Instr] -> [Instr]
instrSS :: [Instr] -> InstrS
instrSS = (++)
instrS :: Instr -> InstrS
instrS = (:)

x86 :: [Instr] -> CM String
x86 ins = return $ (unlines . map show) ins

-- TODO: stack align 16 jeśli trzeba
