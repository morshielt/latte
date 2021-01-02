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
--TODO: zmienne o nazwie self w metodach!
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
--   , ins :: InstrS
  } --deriving Show

-- type CMonad a = RWS CEnv AsmStmts CState a

type CM a = ReaderT CEnv (StateT CState (ExceptT String IO)) a

throwCM :: String -> CM a
throwCM = lift . lift . throwE

compile (Program prog) = evalStateT
    (runReaderT (go prog) (CEnv 0 M.empty))
    (CState 0 0 0 0 0 "" M.empty predefinedFns M.empty M.empty)
  where
    go prog = do
        saveClassesMembers prog
        vmtsCode <- createVMTs
        flip ($) [] <$> translate vmtsCode prog >>= x86
    predefinedFns :: M.Map Var Type
    predefinedFns = M.fromList
        [ ("printInt"     , Void)
        , ("printString"  , Void)
        , ("error"        , Void)
        , ("readInt"      , Int)
        , ("readString"   , Str)
        , ("concatStrings", Str) --TODO: nazwa lepsza czy coś
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
    Decl t ds -> do
        env <- ask
        foldM (goDecl t) (env, id) ds

    Ass ass e -> do
        accCode  <- transAccessible ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        exprCode <- transExpr e
        env      <- ask
        return
            ( env
            , accCode . exprCode . instrSS
                [POP $ Reg EAX, POP $ Reg EDX, MOV (Reg EAX) $ Addr 0 EDX]
            )
    Incr ass -> do
        accCode <- transAccessible ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env     <- ask
        return (env, accCode . instrSS [POP $ Reg EAX, UnIns INC $ Addr 0 EAX])
    Decr ass -> do
        accCode <- transAccessible ass -- TODO: tablice/pole ogarnąć instrukcje kolejność no
        env     <- ask
        return (env, accCode . instrSS [POP $ Reg EAX, UnIns DEC $ Addr 0 EAX])
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
        defaultValue _    = return nullPtr -- StrLit <$> getStrLabel ""
        -- defaultValue x =
        --     throwCM $ "defaultValue for " ++ show x ++ " not impl yet"

nullPtr = Lit 0

transAccessible :: Expr -> CM InstrS
-- assignable
transAccessible (EVar (Ident var)) = do
    env <- ask
    case M.lookup var (varMem env) of --TODO:atrybut
        Nothing ->
            throwCM $ "Impossible transExpr (EVar (Ident var))" ++ show var
        Just (loc, _) -> case loc of
            Attribute l ->
                return
                    $ instrSS
                          [ MOV (Mem $ Param 1) $ Reg EAX
                          , LEA (Mem loc) $ Reg EDX
                          , PUSH $ Reg EDX
                          ] -- Param 1 = self
            _ -> return $ instrSS [LEA (Mem loc) $ Reg EAX, PUSH $ Reg EAX]
                -- return $ instrS $ PUSH $ Mem loc

-- TODO: tablice/pole ogarnąć instrukcje kolejność no

transAccessible (EAttrAcc expr (Ident attr)) = do
    let code i = case expr of
            EApp{}           -> accessibleCode i
            EMethCall{}      -> accessibleCode i -- TODO: sprawdzić
            ENew _ ClsNotArr -> accessibleCode i
            _                -> assignableCode i
    Cls (Ident cls) <- getExprType expr --TODO: pattern matching wysypany?
    accCode         <- transAccessible expr
    vmts            <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible transEAttrAcc vmts"
        Just vmt -> case M.lookup attr $ vattrs vmt of
            Nothing               -> throwCM "Impossible transEAttrAcc cls"
            Just (Attribute i, _) -> return $ accCode . code i
  where
    accessibleCode i =
        instrSS [POP $ Reg EAX, LEA (AttrAddr i EAX) $ Reg EDX, PUSH $ Reg EDX]
    assignableCode i = instrSS
        [ POP $ Reg EAX
        , MOV (Addr 0 EAX) $ Reg EDX
        , LEA (AttrAddr i EDX) $ Reg EAX
        , PUSH $ Reg EAX
        ]

-- -- accessible
transAccessible (EMethCall expr (Ident name) es) = do
    -- let code i = case expr of
    --         EApp{}           -> accessibleCode i
    --         EMethCall{}      -> accessibleCode i -- TODO: sprawdzić
    --         ENew _ ClsNotArr -> accessibleCode i
    --         _                -> assignableCode i
    Cls (Ident cls) <- getExprType expr
    accCode         <- transAccessible expr
    es'             <- mapM transExpr es
    let ess = foldr (.) id (reverse es')
    vmts <- gets vmts
    --TODO: jak fcja/metoda zwraca void to nie pushujemy EAX!
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible transAccessible EMethCall"
        Just vmt -> do
            (offset, methodOwner, pushReturn) <-
                case M.lookup name (M.fromList $ vmeths vmt) of
                    Nothing ->
                        throwCM "Impossible transAccessible EMethCall name"
                    Just (Fun t _, offset, methodOwner) -> if t == Void
                        then do
                            throwCM "How would you use void as lvalue?"
                            return (offset, methodOwner, id)
                        else
                            return
                                ( offset
                                , methodOwner
                                , instrS $ PUSH $ Addr 0 EAX
                                )

            return
                $ ess
                . accCode
                -- . code
                . instrSS
                      [ -- PUSH $ Mem $ Local 1 -- SELF , 
                    --     CALL (methodLabel methodOwner name)
                    --   $ fromIntegral
                    --   $ length es --TODO:FIXME: CALL metoedy z VTABLE A NIE NA PAŁĘ!!! i inicjalizować vtable przy new!!!
                        POP $ Reg EAX
                    --   , PUSH $ Reg EAX
                      , PUSH $ Reg EAX
                    --   , LEA (Addr 0 EAX) (Reg EAX)
                    --   , LEA (Addr 0 EAX) (Reg EAX)
                      , MOV (Addr 0 EAX) (Reg EAX)
                    --   , 
                      , CALLM (MethAddr offset EAX) $ fromIntegral $ length es --TODO:FIXME: CALL metoedy z VTABLE A NIE NA PAŁĘ!!! i inicjalizować vtable przy new!!!
                      , BinIns
                              ADD
                              (Lit (dword * (1 + fromIntegral (length es))))
                          $ Reg ESP
                      ]
                . pushReturn
--   where
--     accessibleCode i =
--         instrSS [POP $ Reg EAX, LEA (AttrAddr i EAX) $ Reg EDX, PUSH $ Reg EDX]
--     assignableCode i = instrSS
--         [ POP $ Reg EAX
--         , MOV (Addr 0 EAX) $ Reg EDX
--         , LEA (AttrAddr i EDX) $ Reg EAX
--         , PUSH $ Reg EAX
--         ]

transAccessible (EApp (Ident var) es) = do
    es' <- mapM transExpr es
    let ess = foldr (.) id (reverse es')
    funRet  <- gets funRet
    retCode <- case M.lookup var funRet of
        Nothing -> throwCM "How would you use void as lvalue?//2"
        Just t ->
            if t == Void then return id else return $ instrS $ PUSH $ Addr 0 EAX
    return
        $ ess
        . instrSS
              [ CALL var $ fromIntegral $ length es
              , BinIns ADD (Lit (dword * fromIntegral (length es))) $ Reg ESP
              ]
        . retCode

transAccessible (ENew (Cls (Ident clsName)) ClsNotArr) = do
    vmts <- gets vmts
    case M.lookup clsName vmts of
        Nothing  -> throwCM "Impossible ENew Class"
        Just vmt -> do
            let numMem = fromIntegral $ M.size $ vattrs vmt
            return $ instrSS
                [ PUSH $ Lit dword
                , PUSH $ Lit numMem
                , CALL "calloc" 2
                , BinIns ADD (Lit $ dword * 2) $ Reg ESP
                , MOV (VTMLit $ vmtLabel clsName) $ Addr 0 EAX
                , PUSH $ Reg EAX
                ]
transAccessible e =
    throwCM $ "Not an transAccessible or not implemented " ++ show e

--TODO: return expr w eax i wtedy push tylko jak złożony i potem brać bez popa tylko od razu z eax ogar.
--TODO: na koniec: spróbować zamienić PUSH rzecz na MOV rzecz do EAX, a w stmtach pop na użycie EAX bezpośrednie
transExpr :: Expr -> CM InstrS

-- assignables
transExpr (EVar (Ident var)) = do
    -- sco <- asks scope
    -- loc <- findInAnyScope var sco
    env <- ask
    case M.lookup var (varMem env) of --TODO:atrybut
        Nothing       -> throwCM "Impossible transExpr (EVar (Ident var))"
        Just (loc, _) -> case loc of
            Attribute l ->
                return $ instrSS [MOV (Mem $ Param 1) $ Reg EAX, PUSH $ Mem loc] -- Param 1 = self
            _ -> return $ instrS $ PUSH $ Mem loc

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
        return $ accCode . instrSS [POP $ Reg EAX, PUSH $ Addr 0 EAX]

-- accessibles
transExpr (EMethCall expr (Ident name) es) = do
    Cls (Ident cls) <- getExprType expr
    accCode         <- transExpr expr
    es'             <- mapM transExpr es
    let ess = foldr (.) id (reverse es')
    vmts <- gets vmts
    --TODO: jak fcja/metoda zwraca void to nie pushujemy EAX!
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible transAccessible EMethCall"
        Just vmt -> do
            (offset, methodOwner, pushReturn) <-
                case M.lookup name (M.fromList $ vmeths vmt) of
                    Nothing ->
                        throwCM "Impossible transAccessible EMethCall name"
                    Just (Fun t _, offset, methodOwner) -> if t == Void
                        then return (offset, methodOwner, id)
                        else return
                            (offset, methodOwner, instrS $ PUSH $ Reg EAX)

            return
                $ ess
                . accCode
                . instrSS
                      [ -- PUSH $ Mem $ Local 1 -- SELF , 
                        POP $ Reg EAX
                    --   , PUSH $ Reg EAX
                      , PUSH $ Reg EAX
                    --   , LEA (Addr 0 EAX) (Reg EAX)
                    --   , LEA (Addr 0 EAX) (Reg EAX)
                      , MOV (Addr 0 EAX) (Reg EAX)
                    --   , 
                      , CALLM (MethAddr offset EAX) $ fromIntegral $ length es --TODO:FIXME: CALL metoedy z VTABLE A NIE NA PAŁĘ!!! i inicjalizować vtable przy new!!!
                      , BinIns
                              ADD
                              (Lit (dword * (1 + fromIntegral (length es))))
                          $ Reg ESP
                      ]
                . pushReturn

transExpr e@(EApp (Ident var) es) = do
    es' <- mapM transExpr es
    let ess = foldr (.) id (reverse es')
    funRet  <- gets funRet
    retCode <- case M.lookup var funRet of
        Nothing -> throwCM "Impossible transAccessible EApp var"
        Just t ->
            if t == Void then return id else return $ instrS $ PUSH $ Reg EAX
    return
        $ ess
        . instrSS
              [ CALL var $ fromIntegral $ length es
              , BinIns ADD (Lit (dword * fromIntegral (length es))) $ Reg ESP
              ]
        . retCode

transExpr (ENew (Cls (Ident clsName)) ClsNotArr) = do
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
                , PUSH $ Reg EAX
                ]






-----------------------------------------------------------------------------------------------------------------

transExpr (ECastNull _  ) = return $ instrS $ PUSH nullPtr

transExpr (EString   str) = do
    index <- getStrLabel str
    return $ instrS $ PUSH $ StrLit index
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

getStrLabel :: String -> CM Integer
getStrLabel str = do
    strs <- gets strings
    case M.lookup str strs of
        Nothing -> do
            let i = fromIntegral $ M.size strs
            modify (\st -> st { strings = M.insert str (StrLabel i str) strs })
            return i
        Just (StrLabel i str) -> return i

getExprType :: Expr -> CM Type
getExprType (EVar (Ident var)) = do
    env <- ask
    case M.lookup var (varMem env) of
        Nothing ->
            throwCM $ "Impossible getExprType (EVar (Ident var)) " ++ var
        Just (_, t) -> return t

getExprType (ELitInt _) = return Int

getExprType ELitTrue    = return Bool

getExprType ELitFalse   = return Bool

getExprType (ENew (Cls (Ident clsName)) ClsNotArr) =
    return $ Cls (Ident clsName)

-- getExprType (ENewArr t     _          ) = return (ArrType t)

getExprType (EApp (Ident ident) _) = do
    state <- get
    case M.lookup ident (funRet state) of
        Nothing -> throwCM "Impossible getExprType (EApp (Ident ident) _))"
        Just t  -> return t

-- getExprType (EPropApp expr ident _    ) = do
--     (ClsType t) <- getExprType expr
--     clt         <- getClassType t
--     return $ retType $ case M.lookup ident (fenv clt) of
--         (Just x) -> x
--         Nothing  -> error "Fun in cls fenv lookup!"

getExprType (EAttrAcc expr (Ident attr)) = do
    Cls (Ident cls) <- getExprType expr --TODO: pattern matching wysypany?
    accCode         <- transAccessible expr
    vmts            <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible getExprType vmts"
        Just vmt -> case M.lookup attr $ vattrs vmt of
            Nothing     -> throwCM "Impossible getExprType cls"
            Just (_, t) -> return t

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
getExprType x                = throwCM $ show x
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
    show (VMTable ms               ) = ".int " ++ intercalate "," ms

dword = 4

type InstrS = [Instr] -> [Instr]
instrSS :: [Instr] -> InstrS
instrSS = (++)
instrS :: Instr -> InstrS
instrS = (:)

x86 :: [Instr] -> CM String
x86 ins = return $ (unlines . map (\x -> "\t" ++ show x)) ins

-- TODO: stack align 16 jeśli trzeba
