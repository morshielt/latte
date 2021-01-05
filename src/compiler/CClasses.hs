module CClasses
    ( createVMTs
    , saveClassesMembers
    , transMethods
    )
where

import           AbsLatte
import           CCommon
import           CStmts

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.List                      ( nubBy )
import           Data.Map                      as M
                                                ( Map
                                                , empty
                                                , lookup
                                                , insert
                                                , fromList
                                                , toList
                                                , union
                                                )

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
      where
        saveClassMember (attrs, meths) member = case member of
            Attr type_ (Ident ident) -> return ((ident, type_) : attrs, meths)
            Meth ret (Ident ident) args _ -> do
                let type_ = Fun ret (map (\(Arg t _) -> t) args)
                return (attrs, (ident, type_) : meths)
        extractExt :: ClassExt -> Maybe Var
        extractExt ext = case ext of
            NoExt              -> Nothing
            Ext (Ident parent) -> Just parent

transMethods :: Var -> ClMember -> CM InstrS
transMethods _   Attr{}                         = return id
transMethods cls (Meth ret (Ident name) args b) = do
    modify
        (\st -> st { locals   = 0
                   , retLabel = "ret______" ++ methodLabel cls name
                   , funRet   = M.insert name ret $ funRet st
                   }
        )
    vmts <- gets vmts
    case M.lookup cls vmts of
        Nothing  -> throwCM "Impossible after typecheck"
        Just vmt -> do
            (_, code) <- do
                let args' = M.fromList $ zipWith
                        (\(Arg t (Ident var)) i -> (var, (Param i, t)))
                        args
                        [2 ..]
                let args'WithSelf =
                        M.insert "self" (Param 1, Cls (Ident cls)) args'
                local
                    (\env -> env { varMem = M.union (vattrs vmt) args'WithSelf }
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


createVMTs :: CM InstrS
createVMTs = do
    cDefs <- gets cDefs
    mapM_ createVMT $ M.toList cDefs
    vmts <- gets vmts
    let clsVmeths = map (\(v, vmt) -> (v, map vmtToLabel (vmeths vmt)))
            $ M.toList vmts
    let notStructs = filter (\(_, meths) -> meths /= []) clsVmeths
    let instrs     = map (uncurry vmtInstr) notStructs
    return $ foldr (.) id instrs
  where
    vmtInstr cls meths =
        instrSS [Lab $ FuncLabel (vmtLabel cls), VMTable meths]
    vmtToLabel (meth, (_, _, methOwner)) = methodLabel methOwner meth

createVMT :: (Var, CDef) -> CM ()
createVMT (cls, cDef) = do
    asms <- getParentMembers (Just cls)
    let (as, ms) = unzip asms
    let
        as' = zipWith (\(k, t) i -> (k, (Attribute i, t)))
                      (concat $ reverse as)
                      [1 ..]
    let ms'       = concat $ reverse ms
    let orderedMs = map fst $ nubBy (\(m1, _) (m2, _) -> m1 == m2) ms'
    let goodClsMs = M.fromList ms'
    let goodMs = zipWith (\(k, (t, v)) i -> (k, (t, i, v)))
                         (map (`lookup'` goodClsMs) orderedMs)
                         [0 ..]
    let vmt = VMT { vattrs = M.fromList as', vmeths = goodMs }
    modify (\st -> st { vmts = M.insert cls vmt (vmts st) })
  where
    lookup' :: Var -> M.Map Var (Type, Var) -> (Var, (Type, Var))
    lookup' k m = case M.lookup k m of
        Nothing     -> error "Impossible after typecheck'"
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
                $ ( M.toList $ attrs cDef
                  , map (\(v, t) -> (v, (t, cls))) (M.toList $ meths cDef)
                  )
                : asms
