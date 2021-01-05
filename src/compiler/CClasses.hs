module CClasses where

import           AbsLatte
import           PrintLatte
-- import           SACommon                       ( TCType )
import           CCommon
-- import           CExprs
import           CStmts
-- import           CClasses

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
    let
        instrs =
            map
                    (\(cls, meths) -> instrSS
                        [Lab $ FuncLabel (vmtLabel cls), VMTable meths]
                    )
                $ filter (\(_, meths) -> meths /= []) clsVmeths
    return $ foldr (.) id instrs




createVMT :: (Var, CDef) -> CM () --TODO: można odkwadracić jak bd obliczać dla parentów przede mną i korzystać z ich wyniku
createVMT (cls, cDef) = do
    let vmt = VMT { vmeths = [], vattrs = M.empty }
    asms <- getParentMembers (Just cls)
    let (as, ms) = unzip asms
    let
        as' = zipWith (\(k, t) i -> (k, (Attribute i, t)))
                      (concat $ reverse as)
                      [1 ..] -- DONE: od 1 bo 0 to adres Vtable? a co jak nie ma żadnych metod? też vtable?
    let ms'       = concat $ reverse ms
    let orderedMs = map fst $ nubBy (\(m1, _) (m2, _) -> m1 == m2) ms'
    let goodClsMs = M.fromList ms'
    let goodMs = zipWith (\(k, (t, v)) i -> (k, (t, i, v)))
                         (map (`lookup'` goodClsMs) orderedMs)
                         [0 ..]
    let vmt = VMT { vattrs = M.fromList as', vmeths = goodMs }
    -- liftIO $ print $ M.fromList as'
    -- liftIO $ print goodMs
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
        Attr type_ (Ident ident)      -> return ((ident, type_) : attrs, meths) -- DONE: [niby działa] spr. czy dodawanie przez : działa tak samo (bo by lepsze było)
        Meth ret (Ident ident) args _ -> do
            let type_ = Fun ret (map (\(Arg t _) -> t) args)
            return (attrs, (ident, type_) : meths)



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
                                     [2 ..]
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

