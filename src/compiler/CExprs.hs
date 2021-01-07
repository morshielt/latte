module CExprs
    ( getExprType
    , transCond
    , transExpr
    , transLValue
    )
where

import           AbsLatte
import           CCommon

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Map                      as M
                                                ( Map
                                                , lookup
                                                , insert
                                                , size
                                                , fromList
                                                )

-- expr type getters --------------------------------------
getExprType :: Expr -> CM Type
getExprType (EVar (Ident var)              ) = snd <$> getVar var
getExprType (EAttrAcc expr (Ident "length")) = do
    t <- getExprType expr
    case t of
        (Arr t_) -> return t_
        _        -> snd <$> getVmtAttr expr "length"
getExprType (EAttrAcc expr  (Ident attr)) = snd <$> getVmtAttr expr attr
getExprType (EArrAcc  expr1 _           ) = do
    (Arr t) <- getExprType expr1
    return t
getExprType (EMethCall expr (Ident name) es) = do
    (Fun t _, offset, _) <- getVmtMeth expr name
    return t
getExprType (EApp (Ident ident) _        ) = getFunRet ident
getExprType (ENew cls           ClsNotArr) = return cls
getExprType (ECastNull (Cls ident)       ) = return $ Cls ident
getExprType (ECastNull (Arr t    )       ) = return (Arr t)
getExprType ELitInt{}                      = return Int
getExprType ELitTrue                       = return Bool
getExprType ELitFalse                      = return Bool
getExprType EString{}                      = return Str
getExprType Neg{}                          = return Int
getExprType Not{}                          = return Bool
getExprType EMul{}                         = return Int
getExprType (EAdd e Plus  _)               = getExprType e
getExprType (EAdd e Minus _)               = return Int
getExprType ERel{}                         = return Bool
getExprType EAnd{}                         = return Bool
getExprType EOr{}                          = return Bool
getExprType (ENew type_ (ArrSize _))       = return $ Arr type_

-- lvalues  ------------------------------------------------
transLValue :: Expr -> CM InstrS
-- assignables
transLValue (EVar (Ident var)) = transEVar var attrCode locCode
  where
    attrCode loc =
        [ MOV (Mem $ Param 1) $ Reg EAX
        , LEA (Mem loc) $ Reg EDX
        , MOV (Reg EDX) (Reg EAX)
        ]
    locCode loc = [LEA (Mem loc) $ Reg EAX]

transLValue (EAttrAcc expr (Ident attr)) = do
    accCode          <- transLValue expr
    (Attribute i, _) <- getVmtAttr expr attr
    return $ accCode . code i
  where
    code i = case expr of
        EApp{}      -> accessibleCode i
        EMethCall{} -> accessibleCode i
        ENew{}      -> accessibleCode i
        _           -> assignableCode i
    accessibleCode i = instrSS [LEA (AttrAddr i EAX) $ Reg EAX]
    assignableCode i =
        instrSS [MOV (Addr 0 EAX) $ Reg EDX, LEA (AttrAddr i EDX) $ Reg EAX]

transLValue (EArrAcc accExpr indexExpr) = do
    indexCode <- transExpr indexExpr
    accCode   <- transLValue accExpr
    return $ indexCode . instrS (PUSH (Reg EAX)) . accCode . code
  where
    code = case accExpr of
        EApp{}      -> accessibleCode
        EMethCall{} -> accessibleCode
        ENew{}      -> accessibleCode
        _           -> assignableCode
    accessibleCode = instrSS
        [ POP (Reg EDX)
        , UnIns INC (Reg EDX)
        , LEA (ArrElemAddr EAX EDX dword) $ Reg EAX
        ]
    assignableCode = instrSS
        [ POP (Reg EDX)
        , UnIns INC (Reg EDX)
        , MOV (Addr 0 EAX) $ Reg EAX
        , LEA (ArrElemAddr EAX EDX dword) $ Reg EAX
        ]

-- accessibles
transLValue (EMethCall expr (Ident name) es) = do
    (Fun t _, offset, _) <- getVmtMeth expr name
    accCode              <- transExpr expr
    es'                  <- mapM transExpr es
    let argsCode =
            foldr (\x acc -> x . instrS (PUSH $ Reg EAX) . acc) id (reverse es')
    return $ argsCode . accCode . instrSS
        [ PUSH $ Reg EAX
        , MOV (Addr 0 EAX) (Reg EAX)
        , CALLM (MethAddr offset EAX)
        , BinIns ADD (Lit (dword * (1 + fromIntegral (length es)))) $ Reg ESP
        ]

transLValue (EApp (Ident var) es) = do
    inClassMethod <- asks inClassMethod
    case inClassMethod of
        Nothing  -> handleEAppLValue
        Just cls -> do
            vmts <- gets vmts
            case M.lookup cls vmts of
                Nothing  -> throwCM "Impossible after type check"
                Just vmt -> case M.lookup var $ M.fromList $ vmeths vmt of
                    Nothing -> handleEAppLValue
                    Just _  -> transLValue
                        (EMethCall (EVar (Ident "self")) (Ident var) es)
  where
    handleEAppLValue = do
        es' <- mapM transExpr es
        let
            argsCode = foldr (\x acc -> x . instrS (PUSH $ Reg EAX) . acc)
                             id
                             (reverse es')
        t <- getFunRet var
        return $ argsCode . instrSS
            [ CALL var
            , BinIns ADD (Lit (dword * fromIntegral (length es))) $ Reg ESP
            ]

transLValue e@(ENew (Cls (Ident clsName)) ClsNotArr) = do
    vmt <- getVmts e
    let numMem = (1 +) $ fromIntegral $ M.size $ vattrs vmt
    let vtable = if vmeths vmt /= []
            then instrS $ MOV (VTMLit $ vmtLabel clsName) $ Addr 0 EAX
            else id
    return
        $ instrSS
              [ PUSH $ Lit dword
              , PUSH $ Lit numMem
              , CALL "calloc"
              , BinIns ADD (Lit $ dword * 2) $ Reg ESP
              ]
        . vtable

transLValue (ENew type_ (ArrSize sizeExpr)) = do
    sizeCode <- transExpr sizeExpr
    return $ sizeCode . instrSS
        [ PUSH $ Reg EAX
        , UnIns INC (Reg EAX)
        , PUSH $ Lit dword
        , PUSH $ Reg EAX
        , CALL "calloc"
        , BinIns ADD (Lit $ dword * 2) $ Reg ESP
        , POP (Reg EDX)
        , MOV (Reg EDX) (Addr 0 EAX)
        ]

transEVar :: Var -> (Memory -> [Instr]) -> (Memory -> [Instr]) -> CM InstrS
transEVar var attrCode locCode = do
    (loc, _) <- getVar var
    env      <- ask
    case loc of
        Attribute _ -> return $ instrSS $ attrCode loc
        _           -> return $ instrSS $ locCode loc

-- expressions --------------------------------------------
transExpr :: Expr -> CM InstrS
transExpr (EVar (Ident var)) = transEVar var attrCode locCode
  where
    attrCode loc = [MOV (Mem $ Param 1) $ Reg EAX, MOV (Mem loc) (Reg EAX)]
    locCode loc = [MOV (Mem loc) (Reg EAX)]
transExpr eattr@(EAttrAcc expr (Ident ident)) = do
    type_ <- getExprType expr
    case type_ of
        (Arr _) -> transExpr (EArrAcc expr (ELitInt (-1)))
        _       -> do
            accCode <- transLValue eattr
            return $ accCode . instrSS [MOV (Addr 0 EAX) (Reg EAX)]
transExpr earracc@(EArrAcc expr1 expr2) = do
    accCode <- transLValue earracc
    return $ accCode . instrSS [MOV (Addr 0 EAX) (Reg EAX)]

transExpr e@(EMethCall expr (Ident name) es) = transLValue e
transExpr e@(EApp (Ident var) es)            = transLValue e
transExpr e@(ENew (Cls (Ident clsName)) ClsNotArr) = transLValue e
transExpr e@(ENew type_ (ArrSize sizeExpr))  = transLValue e

transExpr (ECastNull _) = return $ instrS $ MOV nullPtr (Reg EAX)
transExpr (  EString   str                 ) = do
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
    return $ code . instrSS [UnIns NEG $ Reg EAX]
transExpr (Not e) = do
    code <- transExpr e
    return $ code . instrSS [BinIns XOR (Lit 1) $ Reg EAX]
transExpr (EAdd e1 op e2) = do
    t <- getExprType e1
    case t of
        Str -> transExpr (EApp (Ident "concatStrings_____") [e1, e2])
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
transExpr e@(ERel e1 op e2) = do
    t <- getExprType e1
    case t of
        Str -> do
            let cmp = EApp (Ident "compareStrings_____") [e1, e2]
            cmpCall    <- transExpr cmp
            trueLabel  <- getFreeLabel
            afterLabel <- getFreeLabel
            return $ cmpCall . instrSS
                [ BinIns CMP (Lit 0) (Reg EAX)
                , Jump (chooseOp op) $ JmpLabel trueLabel
                , MOV falseLit (Reg EAX)
                , Jump JMP $ JmpLabel afterLabel
                , Lab $ JmpLabel trueLabel
                , MOV trueLit (Reg EAX)
                , Lab $ JmpLabel afterLabel
                ]
        _ -> transRelOp e1 op e2
  where
    transRelOp e1 op e2 = do
        falseLabel <- getFreeLabel
        trueLabel  <- getFreeLabel
        afterLabel <- getFreeLabel
        code       <- transCond e trueLabel falseLabel
        return $ code . instrSS
            [ Lab $ JmpLabel falseLabel
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
    return $ code . instrSS
        [ Lab $ JmpLabel trueLabel
        , MOV trueLit (Reg EAX)
        , Jump JMP $ JmpLabel afterLabel
        , Lab $ JmpLabel falseLabel
        , MOV falseLit (Reg EAX)
        , Lab $ JmpLabel afterLabel
        ]
transExpr e@(EOr e1 e2) = do
    falseLabel <- getFreeLabel
    trueLabel  <- getFreeLabel
    afterLabel <- getFreeLabel
    code       <- transCond e trueLabel falseLabel
    return $ code . instrSS
        [ Lab $ JmpLabel falseLabel
        , MOV falseLit (Reg EAX)
        , Jump JMP $ JmpLabel afterLabel
        , Lab $ JmpLabel trueLabel
        , MOV trueLit (Reg EAX)
        , Lab $ JmpLabel afterLabel
        ]

binOp :: [Instr] -> InstrS -> InstrS
binOp ops ret = instrSS ((POP $ Reg ECX) : ops) . ret

transBinOp :: Expr -> Expr -> InstrS -> CM InstrS
transBinOp e1 e2 opCode = do
    code1 <- transExpr e1
    code2 <- transExpr e2
    return $ code1 . instrS (PUSH $ Reg EAX) . code2 . opCode . instrS
        (MOV (Reg ECX) (Reg EAX))

-- jumping code generation
transCond :: Expr -> Integer -> Integer -> CM InstrS
transCond e@(ERel e1 op e2) lThen lElse = do
    t <- getExprType e1
    case t of
        Str -> do
            let cmp = EApp (Ident "compareStrings_____") [e1, e2]
            cmpCall <- transExpr cmp
            return $ cmpCall . instrSS
                [ BinIns CMP (Lit 0) (Reg EAX)
                , Jump (chooseOp op) $ JmpLabel lThen
                , Jump JMP $ JmpLabel lElse
                ]
        _ -> transCondRel e1 op e2
  where
    transCondRel e1 op e2 = do
        e1Code <- transExpr e1
        e2Code <- transExpr e2
        return $ e1Code . instrS (PUSH $ Reg EAX) . e2Code . instrSS
            [ MOV (Reg EAX) (Reg ECX)
            , POP $ Reg EAX
            , BinIns CMP (Reg ECX) $ Reg EAX
            , Jump (chooseOp op) $ JmpLabel lThen
            , Jump JMP $ JmpLabel lElse
            ]
transCond (EAnd c1 c2) lTrue lFalse = do
    lMid  <- getFreeLabel
    code1 <- transCond c1 lMid lFalse
    code2 <- transCond c2 lTrue lFalse
    return $ code1 . instrS (Lab $ JmpLabel lMid) . code2
transCond (EOr c1 c2) lTrue lFalse = do
    lMid  <- getFreeLabel
    code1 <- transCond c1 lTrue lMid
    code2 <- transCond c2 lTrue lFalse
    return $ code1 . instrS (Lab $ JmpLabel lMid) . code2
transCond (Not c)   lTrue lFalse = transCond c lFalse lTrue

transCond ELitTrue  lTrue lFalse = return $ instrS (Jump JMP $ JmpLabel lTrue)
transCond ELitFalse lTrue lFalse = return $ instrS (Jump JMP $ JmpLabel lFalse)
transCond e         lTrue lFalse = do
    code <- transExpr e
    return $ code . instrSS
        [ BinIns CMP trueLit (Reg EAX)
        , Jump JE $ JmpLabel lTrue
        , Jump JMP $ JmpLabel lFalse
        ]

-- env/state getters ---------------------------------------
getVmts :: Expr -> CM VMT
getVmts expr = do
    Cls (Ident cls) <- getExprType expr
    vmts            <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible after type check"
        Just vmt -> return vmt

getVmtAttr :: Expr -> Var -> CM (Memory, Type)
getVmtAttr expr attr = do
    vmt <- getVmts expr
    case M.lookup attr $ vattrs vmt of
        Nothing -> throwCM "Impossible after type check"
        Just it -> return it

getVmtMeth :: Expr -> Var -> CM (Type, Integer, Var)
getVmtMeth expr meth = do
    vmt <- getVmts expr
    case M.lookup meth $ M.fromList $ vmeths vmt of
        Nothing  -> throwCM "Impossible after type check"
        Just tiv -> return tiv

getFunRet :: Var -> CM Type
getFunRet var = do
    funRet <- gets funRet
    case M.lookup var funRet of
        Nothing -> throwCM "Impossible after type check"
        Just t  -> return t

getVar :: Var -> CM (Memory, Type)
getVar var = do
    env <- ask
    case M.lookup var (varMem env) of
        Nothing -> throwCM "Impossible after type check"
        Just mt -> return mt
