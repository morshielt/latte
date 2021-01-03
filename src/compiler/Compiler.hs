module Compiler
    ( compile
    , x86
    )
where

import           AbsLatte
import           SACommon                       ( TCType )

import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Trans.Except
import           Data.Bits                      ( (.&.) )
import           Data.List                      ( nubBy
                                                , intercalate
                                                )
import           Data.Map                      as M
                                                ( Map
                                                , empty
                                                , lookup
                                                , insert
                                                , size
                                                , elems
                                                , fromList
                                                , toList
                                                , union
                                                )
--TODO: wywołanie error() liczy się jako return w return checkerze!!!
--DONE: spr w typecheck czy ktoś nie deklaruje klasy 'bool' 'int' czy coś XDDD nie da się
--DONE: zmienne o nazwie self w metodach!
--TODO: porównanie stringów to porównanie referencji czy zawartości?
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

compile (Program prog) = evalStateT
    (runReaderT (go prog) (CEnv 0 M.empty))
    (CState 0 0 0 0 0 "" M.empty predefinedFns M.empty M.empty Nothing Nothing)
  where
    go prog = do
        saveClassesMembers prog
        vmtsCode <- createVMTs
        flip ($) [] <$> translate vmtsCode prog >>= x86
    predefinedFns :: M.Map Var Type
    predefinedFns = M.fromList
        [ ("printInt"   , Void)
        , ("printString", Void)
        , ("error"      , Void)
        , ("readInt"    , Int)
        , ("readString" , Str)
        , ( "concatStrings"
          , Str
          ) --TODO: nazwa lepsza czy coś
        , ("compareStrings", Bool) --TODO: nazwa lepsza czy coś
        ]

createVMTs :: CM InstrS
createVMTs = do
    cDefs <- gets cDefs
    mapM_ createVMT $ M.toList cDefs
    vmts <- gets vmts
    let
        clsVmeths =
            map
                    (\(v, vmt) ->
                        ( v
                        , map
                            (\(meth, (_, _, methOwner)) ->
                                methodLabel methOwner meth
                            )
                            (vmeths vmt)
                        )
                    )
                $ M.toList vmts
    -- let instrs = map (\cls meths -> [Label vmtLabel cls, VTable meths] clsVmeths
    let instrs = map
            (\(cls, meths) ->
                instrSS [Lab $ FuncLabel (vmtLabel cls), VMTable meths]
            )
            clsVmeths
    return $ foldr (.) id instrs


vmtLabel :: Var -> String
vmtLabel cls = methodLabel cls "VMT"

createVMT :: (Var, CDef) -> CM () --TODO: można odkwadracić jak bd obliczać dla parentów przede mną i korzystać z ich wyniku
createVMT (cls, cDef) = do
    let vmt = VMT { vmeths = [], vattrs = M.empty }
    asms <- getParentMembers (Just cls)
    let (as, ms) = unzip asms
    let
        as' = zipWith (\(k, t) i -> (k, (Attribute i, t)))
                      (concat $ reverse as)
                      [1 ..] -- TODO: od 1 bo 0 to adres Vtable? a co jak nie ma żadnych metod? też vtable?
    let ms'       = concat $ reverse ms
    let orderedMs = map fst $ nubBy (\(m1, _) (m2, _) -> m1 == m2) ms'
    let goodClsMs = M.fromList ms'
    let goodMs = zipWith (\(k, (t, v)) i -> (k, (t, i, v)))
                         (map (`lookup'` goodClsMs) orderedMs)
                         [0 ..]
    let vmt = VMT { vattrs = M.fromList as', vmeths = goodMs }
    liftIO $ print $ M.fromList as'
    liftIO $ print goodMs
    modify (\st -> st { vmts = M.insert cls vmt (vmts st) })
    return ()

lookup' :: Var -> M.Map Var (Type, Var) -> (Var, (Type, Var))
lookup' k m = case M.lookup k m of
    Nothing     -> error "Impossible lookup'"
    Just (t, v) -> (k, (t, v))

getParentMembers :: Maybe String -> CM [([(Var, Type)], [(Var, (Type, Var))])]
getParentMembers Nothing    = return [([], [])]
getParentMembers (Just cls) = do
    cDefs <- gets cDefs
    case M.lookup cls cDefs of
        Nothing   -> throwCM "Impossible, parent must exist"
        Just cDef -> do
            asms <- getParentMembers $ extends cDef
            return
                ( ( M.toList $ attrs cDef
                  , map (\(v, t) -> (v, (t, cls))) (M.toList $ meths cDef)
                  )
                : asms
                )

extractExt :: ClassExt -> Maybe Var
extractExt ext = case ext of
    NoExt              -> Nothing
    Ext (Ident parent) -> Just parent

saveClassesMembers :: [TopDef] -> CM ()
saveClassesMembers = mapM_ saveClassMembers
  where
    saveClassMembers :: TopDef -> CM ()
    saveClassMembers (FnDef ret (Ident name) _ _) = do
        modify (\st -> st { funRet = M.insert name ret $ funRet st })
        return ()
    saveClassMembers (ClDef (Ident ident) classext clmembers) = do
        clss           <- gets cDefs
        (attrs, meths) <- foldM saveClassMember ([], []) clmembers
        let cdef = CDef { extends = extractExt classext
                        , attrs   = M.fromList attrs
                        , meths   = M.fromList meths
                        }
        modify (\st -> st { cDefs = M.insert ident cdef clss })
    saveClassMember
        :: ([(Var, Type)], [(Var, Type)])
        -> ClMember
        -> CM ([(Var, Type)], [(Var, Type)])
    saveClassMember (attrs, meths) member = case member of
        Attr type_ (Ident ident) -> return (attrs ++ [(ident, type_)], meths) -- TODO: spr. czy dodawanie przez : działa tak samo (bo by lepsze było)
        Meth ret (Ident ident) args _ -> do
            let type_ = Fun ret (map (\(Arg t _) -> t) args)
            return (attrs, meths ++ [(ident, type_)])


translate :: InstrS -> [TopDef] -> CM InstrS
translate vmtsCode tds = do
    code <- foldM go vmtsCode tds
    strs <- gets strings
    let strLabels = map Lab $ M.elems strs
    -- TODO: stringi w sekcji .data, sekcja text po nich!
    return $ instrS Intro . instrSS strLabels . code

  where
    go accCode stmt = do
        code <- transTopDef stmt
        return (accCode . code)

transTopDef :: TopDef -> CM InstrS
transTopDef x = case x of
    FnDef ret (Ident name) args b -> do
        modify (\st -> st { locals = 0, retLabel = "ret_" ++ name })
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
    ClDef (Ident clsName) _ clmembers -> do
        x <- mapM (transMethods clsName) clmembers
        return $ foldr (.) id x

transMethods :: Var -> ClMember -> CM InstrS
transMethods _   Attr{}                         = return id
transMethods cls (Meth ret (Ident name) args b) = do
    modify
        (\st -> st { locals   = 0
                   , retLabel = "ret_" ++ methodLabel cls name
                   , funRet   = M.insert name ret $ funRet st
                   }
        )
    vmts <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible transMethods"
        Just vmt -> do
            (_, code) <- local
                (\env -> env
                    { varMem = M.union (vattrs vmt)
                               $ M.insert "self" (Param 1, Cls (Ident cls))
                               $ M.fromList
                               $ zipWith
                                     (\(Arg t (Ident var)) i ->
                                         (var, (Param i, t))
                                     )
                                     args
                                     [2 ..] -- TODO: od 1 czy od 0?}) 
                    }
                )
                (transStmt (BStmt b))
            state <- get
            return
                $ instrSS
                      [ Lab $ FuncLabel $ methodLabel cls name
                      , Prologue
                      , StackAlloc $ locals state
                      ]
                . code
                . instrSS [Lab $ FuncLabel $ retLabel state, Epilogue, ZIns RET]

methodLabel cls method = cls ++ "." ++ method

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
        return (env, code . instrSS [Jump JMP $ FuncLabel lab])
    SExp e -> do
        code <- transExpr e
        env  <- ask
        return (env, code)
    Cond e s -> do
        trueLabel  <- getFreeLabel
        afterLabel <- getFreeLabel

        condCode   <- transCond e trueLabel afterLabel
        trueCode   <- transAsBStmt s --TODO: czy mam porzucić ten env?
        let op =
                -- instrSS
                --         [ BinIns CMP falseLit $ Reg EAX --TODO: test EAX EAX
                --         , Jump JE $ JmpLabel afterLabel
                --         ]
                 instrS (Lab $ JmpLabel trueLabel) . trueCode . instrS
                (Lab $ JmpLabel afterLabel)
        env <- ask
        return (env, condCode . op)
    CondElse e s1 s2 -> do
        trueLabel  <- getFreeLabel
        falseLabel <- getFreeLabel
        afterLabel <- getFreeLabel

        condCode   <- transCond e trueLabel falseLabel
        trueCode   <- transAsBStmt s1
        falseCode  <- transAsBStmt s2
        let op =
                instrS (Lab $ JmpLabel trueLabel)
                    . trueCode
                    . instrS (Jump JMP $ JmpLabel afterLabel)
                    . instrS (Lab $ JmpLabel falseLabel)
                    . falseCode
                    . instrS (Lab $ JmpLabel afterLabel)
        env <- ask
        return (env, condCode . op)
    While e s -> do
        -- trueLabel  <- getFreeLabel
        -- falseLabel <- getFreeLabel
        afterLabel <- getFreeLabel
        condLabel  <- getFreeLabel
        loopLabel  <- getFreeLabel

        condCode   <- transCond e loopLabel afterLabel
        loopCode   <- transAsBStmt s
        env        <- ask
        return
            ( env
            , instrS (Jump JMP $ JmpLabel condLabel)
            . instrS (Lab $ JmpLabel loopLabel)
            . loopCode
            . instrS (Lab $ JmpLabel condLabel)
            . condCode
            . instrS (Lab $ JmpLabel afterLabel)
            -- . instrSS
            --       [BinIns CMP trueLit $ Reg EAX, Jump JE $ JmpLabel loopLabel]
            )
    Decl t ds -> do
        env <- ask
        foldM (goDecl t) (env, id) ds

    Ass ass e -> do
        accCode  <- transAccessible ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        exprCode <- transExpr e
        env      <- ask
        return
            ( env
            , accCode . instrS (PUSH $ Reg EAX) . exprCode . instrSS
                [POP $ Reg EDX, MOV (Reg EAX) $ Addr 0 EDX]
            )
    Incr ass -> do
        accCode <- transAccessible ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env     <- ask
        return (env, accCode . instrSS [UnIns INC $ Addr 0 EAX])
    Decr ass -> do
        accCode <- transAccessible ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env     <- ask
        return (env, accCode . instrSS [UnIns DEC $ Addr 0 EAX])
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
                return (var, initCode . instrSS [MOV (Reg EAX) (Mem loc)])
        env <- ask
        let envWithDecl = M.insert var (loc, t) $ varMem env
        return (env { varMem = envWithDecl }, code)
      where
        defaultValue :: Type -> CM Operand
        defaultValue Int  = return $ Lit 0
        defaultValue Bool = return falseLit
        defaultValue _    = return nullPtr

nullPtr = Lit 0

getVmts :: Expr -> CM VMT
getVmts expr = do
    Cls (Ident cls) <- getExprType expr --TODO: pattern matching wysypany?
    vmts            <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible transEAttrAcc vmts"
        Just vmt -> return vmt

getVmtAttr :: Expr -> Var -> CM (Memory, Type)
getVmtAttr expr attr = do
    vmt <- getVmts expr
    case M.lookup attr $ vattrs vmt of
        Nothing -> throwCM "Impossible getVmtAttr"
        Just it -> return it

getVmtMeth :: Expr -> Var -> CM (Type, Integer, Var)
getVmtMeth expr meth = do
    vmt <- getVmts expr
    case M.lookup meth $ M.fromList $ vmeths vmt of
        Nothing  -> throwCM "Impossible getVmtMeth"
        Just tiv -> return tiv

getFunRet :: Var -> CM Type
getFunRet var = do
    funRet <- gets funRet
    case M.lookup var funRet of
        Nothing -> throwCM "Jak moxe nie byc takiej funkcji?"
        Just t  -> return t

transAccessible :: Expr -> CM InstrS
-- assignable
transAccessible (EVar (Ident var)) = transEVar var attrCode locCode
  where
    attrCode loc = -- TODO: untested EAXing
        [ MOV (Mem $ Param 1) $ Reg EAX
        , LEA (Mem loc) $ Reg EDX
        , MOV (Reg EDX) (Reg EAX)
        ]
    locCode loc = [LEA (Mem loc) $ Reg EAX]

transAccessible (EAttrAcc expr (Ident attr)) = do
    accCode          <- transAccessible expr
    (Attribute i, _) <- getVmtAttr expr attr
    return $ accCode . code i
  where
    code i = case expr of
        EApp{}           -> accessibleCode i
        EMethCall{}      -> accessibleCode i
        ENew _ ClsNotArr -> accessibleCode i
        _                -> assignableCode i
    accessibleCode i = instrSS [LEA (AttrAddr i EAX) $ Reg EAX]
    assignableCode i = instrSS
        [ --POP $ Reg EAX , 
          MOV (Addr 0 EAX) $ Reg EDX
        , LEA (AttrAddr i EDX) $ Reg EAX
        -- , PUSH $ Reg EAX
        ]

-- -- -- accessible
transAccessible (EMethCall expr (Ident name) es) = do --XXX
    (Fun t _, offset, _) <- getVmtMeth expr name
    accCode              <- transExpr expr
    es'                  <- mapM transExpr es
    let argsCode =
            foldr (\x acc -> x . instrS (PUSH $ Reg EAX) . acc) id (reverse es')
    -- let pushReturn = if t == Void then id else instrS $ PUSH $ Reg EAX
    return $ argsCode . accCode . instrSS
        [ PUSH $ Reg EAX
        , MOV (Addr 0 EAX) (Reg EAX)
        , CALLM (MethAddr offset EAX) $ fromIntegral $ length es
        , BinIns ADD (Lit (dword * (1 + fromIntegral (length es)))) $ Reg ESP
        ]
        -- . pushReturn

transAccessible (EApp (Ident var) es) = do
    es' <- mapM transExpr es
    let argsCode =
            foldr (\x acc -> x . instrS (PUSH $ Reg EAX) . acc) id (reverse es')
    t <- getFunRet var
    return $ argsCode . instrSS
        [ CALL var $ fromIntegral $ length es
        , BinIns ADD (Lit (dword * fromIntegral (length es))) $ Reg ESP
        ]

transAccessible (ENew (Cls (Ident clsName)) ClsNotArr) = do
    vmts <- gets vmts
    case M.lookup clsName vmts of
        Nothing  -> throwCM "Impossible ENew Class"
        Just vmt -> do
            let numMem = (1 +) $ fromIntegral $ M.size $ vattrs vmt
            return $ instrSS
                [ PUSH $ Lit dword
                , PUSH $ Lit numMem
                , CALL "calloc" 2
                , BinIns ADD (Lit $ dword * 2) $ Reg ESP
                , MOV (VTMLit $ vmtLabel clsName) $ Addr 0 EAX
                -- , PUSH $ Reg EAX
                ]

transAccessible e =
    throwCM $ "Not an transAccessible or not implemented " ++ show e

transEVar :: Var -> (Memory -> [Instr]) -> (Memory -> [Instr]) -> CM InstrS
transEVar var attrCode locCode = do
    env <- ask
    case M.lookup var (varMem env) of
        Nothing       -> throwCM "Impossible transExpr (EVar (Ident var))"
        Just (loc, _) -> case loc of
            Attribute _ -> return $ instrSS $ attrCode loc
            _           -> return $ instrSS $ locCode loc

--TODO: return expr w eax i wtedy push tylko jak złożony i potem brać bez popa tylko od razu z eax ogar.
--TODO: na koniec: spróbować zamienić PUSH rzecz na MOV rzecz do EAX, a w stmtach pop na użycie EAX bezpośrednie
transExpr :: Expr -> CM InstrS
-- assignables
transExpr (EVar (Ident var)) = transEVar var attrCode locCode
  where
      --TODO: może nie pójść EAXing! może LEA trzeba
    attrCode loc = [MOV (Mem $ Param 1) $ Reg EAX, MOV (Mem loc) (Reg EAX)]
    locCode loc = [MOV (Mem loc) (Reg EAX)]

transExpr eattr@(EAttrAcc expr (Ident ident))
    | ident == "length" = do
        type_ <- getExprType expr
        case type_ of
            (Arr _) -> throwCM ".length arr unimplemented"
            _       -> transEAttrAcc eattr
    | otherwise = transEAttrAcc eattr
  where
    transEAttrAcc :: Expr -> CM InstrS
    transEAttrAcc eattr = do
        accCode <- transAccessible eattr
        return $ accCode . instrSS [MOV (Addr 0 EAX) (Reg EAX)]

-- -- accessibles
transExpr e@(EMethCall expr (Ident name) es        ) = transAccessible e

transExpr e@(EApp (Ident var            ) es       ) = transAccessible e

transExpr e@(ENew (Cls   (Ident clsName)) ClsNotArr) = transAccessible e

-- -----------------------------------------------------------------------------------------------------------------

transExpr (ECastNull _) = return $ instrS $ MOV nullPtr (Reg EAX) --TODO: unchecked EAXing

transExpr (  EString   str                         ) = do --TODO: unchecked EAXing
    index <- getStrLabel str
    return $ instrS $ MOV (StrLit index) (Reg EAX)
  where
    getStrLabel :: String -> CM Integer
    getStrLabel str = do
        strs <- gets strings
        case M.lookup str strs of
            Nothing -> do
                let i = fromIntegral $ M.size strs
                modify
                    (\st -> st { strings = M.insert str (StrLabel i str) strs })
                return i
            Just (StrLabel i str) -> return i

transExpr (ELitInt n) = return $ instrS $ MOV (Lit n) (Reg EAX)
transExpr ELitTrue    = return $ instrS $ MOV trueLit (Reg EAX)
transExpr ELitFalse   = return $ instrS $ MOV falseLit (Reg EAX)
transExpr (Neg e)     = do
    code <- transExpr e
    return $ code . neg
  where
    neg :: InstrS
    neg = instrSS [UnIns NEG $ Reg EAX]

transExpr (Not e) = do
    code <- transExpr e
    return $ code . not
  where
    not :: InstrS
    not = instrSS [BinIns XOR (Lit 1) $ Reg EAX]

transExpr (EAdd e1 op e2) = do
    t <- getExprType e1
    case t of
        Str -> transExpr (EApp (Ident "concatStrings") [e1, e2])
        _   -> do
            let op' = case op of
                    Plus  -> ADD
                    Minus -> SUB
            transBinOp e1 e2 $ binOp [BinIns op' (Reg EAX) $ Reg ECX] id

transExpr (EMul e1 Times e2) =
    transBinOp e1 e2 $ binOp [BinIns MUL (Reg EAX) $ Reg ECX] id
transExpr (EMul e1 op e2) = do
    let ret = case op of
            Div -> id
            Mod -> instrS $ MOV (Reg EDX) (Reg EAX)
    code1 <- transExpr e1
    code2 <- transExpr e2
    return
        $ code1
        . instrS (PUSH $ Reg EAX)
        . code2
        . instrSS
              [ MOV (Reg EAX) (Reg ECX)
              , POP (Reg EAX)
              , ZIns CDQ
              , BinIns DIV (Reg ECX) $ Reg EAX
              ]
        . ret

transExpr e@(ERel e1 op e2)
    | op `elem` [EQU, NE] = do
        t <- getExprType e1
        case t of
            Str -> do
                let cmp     = EApp (Ident "compareStrings") [e1, e2]
                let trueCmp = if op == NE then Not cmp else cmp
                transExpr trueCmp
            _ -> transRelOp e1 op e2
    | otherwise = transRelOp e1 op e2
  where
    transRelOp e1 op e2 = do
        code1      <- transExpr e1
        code2      <- transExpr e2
        trueLabel  <- getFreeLabel
        afterLabel <- getFreeLabel
        return $ code1 . instrS (PUSH $ Reg EAX) . code2 . instrSS
            [ MOV (Reg EAX) (Reg ECX)
            , POP $ Reg EAX
            , BinIns CMP (Reg ECX) $ Reg EAX
            , Jump (chooseOp op) $ JmpLabel trueLabel
            , MOV falseLit (Reg EAX)
            , Jump JMP $ JmpLabel afterLabel
            , Lab $ JmpLabel trueLabel
            , MOV trueLit (Reg EAX)
            , Lab $ JmpLabel afterLabel
            ]

transExpr e@(EAnd e1 e2) = do
    falseLabel <- getFreeLabel
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel
    code       <- transCond e trueLabel falseLabel

    let trueCode = instrSS
            [ Lab $ JmpLabel trueLabel
            , MOV trueLit (Reg EAX)
            , Jump JMP $ JmpLabel afterLabel
            ]
    let outro = instrSS
            [ Lab $ JmpLabel falseLabel
            , MOV falseLit (Reg EAX)
            , Lab $ JmpLabel afterLabel
            ]
    return $ code . trueCode . outro

transExpr e@(EOr e1 e2) = do
    falseLabel <- getFreeLabel
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel
    code       <- transCond e trueLabel falseLabel

    let falseCode = instrSS
            [ Lab $ JmpLabel falseLabel
            , MOV falseLit (Reg EAX)
            , Jump JMP $ JmpLabel afterLabel
            ]
    let outro = instrSS
            [ Lab $ JmpLabel trueLabel
            , MOV trueLit (Reg EAX)
            , Lab $ JmpLabel afterLabel
            ]
    return $ code . falseCode . outro


transExpr e = throwCM $ show e


-- transCond (CGt e1 e2) lThen lElse = do
--     genExp e1
--     genExp e2
--     emit $ Jif_icmpgt lThen
--     emit $ Jgoto lElse
transCond :: Expr -> Integer -> Integer -> CM InstrS
transCond e@(ERel e1 op e2) lThen lElse
    | op `elem` [EQU, NE] = do
        t <- getExprType e1
        case t of
            Str -> do
                let cmp     = EApp (Ident "compareStrings") [e1, e2]
                let trueCmp = if op == NE then Not cmp else cmp
                transCond trueCmp lThen lElse
            _ -> transCondRel e1 op e2
    | otherwise = transCondRel e1 op e2
  where
    transCondRel e1 op e2 = do
        e1Code <- transExpr e1
        e2Code <- transExpr e2
        return $ e1Code . instrS (PUSH $ Reg EAX) . e2Code . instrSS
            [ MOV (Reg EAX) (Reg ECX)
            , POP $ Reg EAX
            , BinIns CMP (Reg ECX) $ Reg EAX
            , Jump (chooseOp op) $ JmpLabel lThen
                -- , MOV falseLit (Reg EAX)
            , Jump JMP $ JmpLabel lElse
                -- , Lab $ JmpLabel trueLabel
                -- , MOV trueLit (Reg EAX)
                -- , Lab $ JmpLabel afterLabel
            ]


-- transCond (EAnd c1 c2) lTrue lFalse = do
--     lMid <- getFreeLabel
--     transCond c1 lMid lFalse
--     emit $ placeLabel lMid
--     transCond c2 lTrue lFalse
transCond (EAnd c1 c2) lTrue lFalse = do
    lMid  <- getFreeLabel
    code1 <- transCond c1 lMid lFalse
    -- emit $ placeLabel lMid
    code2 <- transCond c2 lTrue lFalse
    return $ code1 . instrS (Lab $ JmpLabel lMid) . code2

transCond ELitTrue lTrue lFalse = return $ instrS (Jump JMP $ JmpLabel lTrue)
transCond ELitFalse lTrue lFalse = return $ instrS (Jump JMP $ JmpLabel lFalse)

-- transCond (COr c1 c2) lTrue lFalse = do
--     lMid <- getFreeLabel
--     transCond c1 lTrue lMid
--     emit $ placeLabel lMid
--     transCond c2 lTrue lFalse
transCond (EOr c1 c2) lTrue lFalse = do
    lMid  <- getFreeLabel
    code1 <- transCond c1 lTrue lMid
    code2 <- transCond c2 lTrue lFalse
    return $ code1 . instrS (Lab $ JmpLabel lMid) . code2

-- transCond (CNot c) lTrue lFalse = genCond c lFalse lTrue
transCond (Not c) lTrue lFalse = transCond c lFalse lTrue

transCond e       lTrue lFalse = transCond (ERel e EQU ELitTrue) lTrue lFalse

binOp ops ret = instrSS ((POP $ Reg ECX) : ops) . ret

transBinOp :: Expr -> Expr -> InstrS -> CM InstrS
transBinOp e1 e2 opCode = do
    code1 <- transExpr e1
    code2 <- transExpr e2
    return $ code1 . instrS (PUSH $ Reg EAX) . code2 . opCode . instrS
        (MOV (Reg ECX) (Reg EAX))


getExprType :: Expr -> CM Type
getExprType (EVar (Ident var)) = do
    env <- ask
    case M.lookup var (varMem env) of
        Nothing ->
            throwCM $ "Impossible getExprType (EVar (Ident var)) " ++ var
        Just (_, t) -> return t

getExprType (EAttrAcc expr (Ident attr)    ) = snd <$> getVmtAttr expr attr

getExprType (EMethCall expr (Ident name) es) = do
    Cls (Ident cls) <- getExprType expr --TODO: pattern matching wysypany?
    accCode         <- transAccessible expr
    vmts            <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible getExprType vmts"
        Just vmt -> case M.lookup name $ M.fromList $ vmeths vmt of
            Nothing              -> throwCM "Impossible getExprType cls"
            Just (Fun t _, _, _) -> return t
getExprType (EApp (Ident ident) _) = do
    state <- get
    case M.lookup ident (funRet state) of
        Nothing -> throwCM "Impossible getExprType (EApp (Ident ident) _))"
        Just t  -> return t
getExprType (ENew cls ClsNotArr) = return cls
getExprType (ECastNull ident   ) = return $ Cls ident
getExprType ELitInt{}            = return Int
getExprType ELitTrue             = return Bool
getExprType ELitFalse            = return Bool
getExprType EString{}            = return Str
getExprType Neg{}                = return Int
getExprType Not{}                = return Bool
getExprType EMul{}               = return Int
getExprType (EAdd e Plus  _)     = getExprType e
getExprType (EAdd e Minus _)     = return Int
getExprType ERel{}               = return Bool
getExprType EAnd{}               = return Bool
getExprType EOr{}                = return Bool
getExprType x                    = throwCM $ show x
-- TODO: jak są stałe, to teoretycznie nie trzebaby ich push/pop tylko wpisać żywcem D: jebać

getFreeLabel :: CM Integer
getFreeLabel = do
    label <- gets freeLabel
    modify (\st -> st { freeLabel = label + 1 })
    return label


trueLit = Lit 1
falseLit = Lit 0

chooseOp op = case op of
    LTH -> JL
    LE  -> JLE
    GTH -> JG
    GE  -> JGE
    EQU -> JE
    NE  -> JNE

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

data Memory = Local Integer | Param Integer | Attribute  Integer
instance Show Memory where
    show (Param     n) = show (dword * (n + 1)) ++ "(" ++ show EBP ++ ")" -- TODO: jeszcze jakoś +/- 4 bo ten adr powr czy co to tam jest czy nie?
    show (Local     n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"
    show (Attribute n) = show (dword * n) ++ "(" ++ show EAX ++ ")" --TODO: check czy EAX ale no powinien.
    -- show (Stack n) = show (-dword * n) ++ "(" ++ show EBP ++ ")"

data Operand = Reg Register | AttrAddr Integer Register | Addr Integer Register | MethAddr Integer Register  | Mem Memory | Lit Integer | StrLit Integer | VTMLit String
instance Show Operand where
    show (Reg r       ) = show r
    show (Addr     0 r) = "(" ++ show r ++ ")"
    show (Addr     i r) = show (-dword * i) ++ "(" ++ show r ++ ")"
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

--TODO: .data
instance Show Instr where
    show Intro = ".text\n.globl main\n"
    show Prologue =
        show (PUSH $ Reg EBP) ++ "\n\t" ++ show (MOV (Reg ESP) $ Reg EBP)
    show (StackAlloc n) = show $ BinIns SUB (Lit (dword * n)) $ Reg ESP --TODO: align 16
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
    show (Lab     l@(StrLabel _i s)) = show l ++ ":\n    .asciz " ++ show s -- ew. .asciz, no idea
    show (Lab     l                ) = show l ++ ":"
    show (VMTable ms               ) = ".int " ++ intercalate ", " ms

dword = 4

type InstrS = [Instr] -> [Instr]
instrSS :: [Instr] -> InstrS
instrSS = (++)
instrS :: Instr -> InstrS
instrS = (:)

indent :: Instr -> String
indent (Lab _) = ""
indent _       = "\t"
x86 :: [Instr] -> CM String
x86 ins = return $ (unlines . map (\x -> indent x ++ show x)) ins

-- DONE: stack align 16 jeśli trzeba [NIE TRZEBA]
