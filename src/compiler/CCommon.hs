module CCommon where

import           AbsLatte

import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                      ( intercalate )
import           Data.Map                      as M
                                                ( Map )

type Var = String
type Offset = Integer
-- type Label = Integer
type Scope = Integer
type VM = M.Map Var (Memory, Type)
type VT = M.Map Var Type
type SL = M.Map String Label
type CD = M.Map Var CDef

data CDef = CDef
    { attrs :: VT
    , meths :: VT
    , extends :: Maybe Var
    }  deriving Show

data VMT = VMT
 {  vmeths :: [ (Var, (Type, Integer, Var))]
    , vattrs :: M.Map Var (Memory, Type)
}

data CEnv = CEnv
  { scope :: Scope
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
  , strings :: SL
  , funRet :: VT
  , cDefs :: CD
  , vmts :: M.Map Var VMT
  , trueLabel ::Maybe Integer
  , falseLabel ::Maybe Integer
--   , ins :: InstrS
  } --deriving Show

-- type CMonad a = RWS CEnv AsmStmts CState a

type CM a = ReaderT CEnv (StateT CState (ExceptT String IO)) a

throwCM :: String -> CM a
throwCM = lift . lift . throwE

trueLit = Lit 1
falseLit = Lit 0
nullPtr = Lit 0

chooseOp op = case op of
    LTH -> JL
    LE  -> JLE
    GTH -> JG
    GE  -> JGE
    EQU -> JE
    NE  -> JNE

data Register = EAX | ECX  | EDX | EBP | ESP
instance Show Register where
    show EBP = "%ebp"
    show ESP = "%esp"
    show EAX = "%eax"
    show EDX = "%edx"
    show ECX = "%ecx"

data Memory = Local Integer | Param Integer | Attribute  Integer
instance Show Memory where
    show (Param     n) = show (dword * (n + 1)) ++ "(" ++ show EBP ++ ")"
    show (Local     n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"
    show (Attribute n) = show (dword * n) ++ "(" ++ show EAX ++ ")"

data Operand = Reg Register
    | AttrAddr Integer Register
    | Addr Integer Register
    | ArrElemAddr Register Register Integer
    | MethAddr Integer Register
    | Mem Memory
    | Lit Integer
    | StrLit Integer
    | VTMLit String
instance Show Operand where
    show (Reg r   ) = show r
    show (Addr 0 r) = "(" ++ show r ++ ")"
    show (Addr i r) = show (-dword * i) ++ "(" ++ show r ++ ")"
    show (ArrElemAddr r1 r2 i) =
        "(" ++ show r1 ++ "," ++ show r2 ++ "," ++ show i ++ ")"
    show (AttrAddr 0 r) = error "Didn't you mean Addr?"
    show (AttrAddr i r) = show (dword * i) ++ "(" ++ show r ++ ")"
    show (MethAddr 0 r) = '*' : "(" ++ show r ++ ")"
    show (MethAddr i r) = '*' : show (dword * i) ++ "(" ++ show r ++ ")"
    show (Mem    m    ) = show m
    show (Lit    l    ) = '$' : show l
    show (VTMLit l    ) = '$' : l
    show (StrLit i    ) = '$' : show (StrLabel i "")

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

data ZOp = RET | CDQ
instance Show ZOp where
    show RET = "ret\n"
    show CDQ = "cdq"

data Label = FuncLabel String | JmpLabel Integer  | StrLabel Integer String
instance Show Label where
    show (FuncLabel f ) = f
    show (JmpLabel  i ) = ".L" ++ show i
    show (StrLabel i _) = ".LC" ++ show i

data Instr = Intro
    | DataSection
    | TextSection
    | Prologue
    | StackAlloc Integer
    | Epilogue
    | CALL String Integer
    | CALLM Operand Integer
    | MOV Operand Operand
    | LEA Operand Operand
    | PUSH Operand
    | POP Operand
    | ARGPUSH Operand
    | Jump JOp Label
    | ZIns ZOp
    | UnIns UnOp Operand
    | BinIns BinOp Operand Operand
    | Lab Label
    | VMTable [String]

instance Show Instr where
    show Intro       = ".globl main"
    show DataSection = ".data"
    show TextSection = "\n.text"
    show Prologue =
        show (PUSH $ Reg EBP) ++ "\n\t" ++ show (MOV (Reg ESP) $ Reg EBP)
    show (StackAlloc n) = show $ BinIns SUB (Lit (dword * n)) $ Reg ESP
    show Epilogue =
        show (MOV (Reg EBP) $ Reg ESP) ++ "\n\t" ++ show (POP $ Reg EBP)
    show (CALL  l _      ) = "call " ++ l
    show (CALLM l _      ) = "call " ++ show l
    show (MOV   o r      ) = "movl " ++ show o ++ ", " ++ show r
    show (LEA   o r      ) = "leal " ++ show o ++ ", " ++ show r
    show (PUSH op        ) = "pushl " ++ show op
    show (POP  op        ) = "popl " ++ show op
    show (ZIns zin       ) = show zin
    show (UnIns unop unin) = show unop ++ " " ++ show unin
    show (Jump  unop unin) = show unop ++ " " ++ show unin
    show (BinIns bop bin1 bin2) =
        show bop ++ " " ++ show bin1 ++ ", " ++ show bin2
    show (Lab     l@(StrLabel _i s)) = show l ++ ":\t.asciz " ++ show s
    show (Lab     l                ) = show l ++ ":"
    show (VMTable ms               ) = ".int " ++ intercalate ", " ms

dword = 4

type InstrS = [Instr] -> [Instr]
instrSS :: [Instr] -> InstrS
instrSS = (++)
instrS :: Instr -> InstrS
instrS = (:)

indent :: Instr -> String
indent Intro       = ""
indent DataSection = ""
indent TextSection = ""
indent (Lab     _) = ""
indent (VMTable _) = ""
indent _           = "\t"


vmtLabel :: Var -> String
vmtLabel cls = methodLabel cls "VMT"

methodLabel cls method = cls ++ "." ++ method

getFreeLabel :: CM Integer
getFreeLabel = do
    label <- gets freeLabel
    modify (\st -> st { freeLabel = label + 1 })
    return label
