{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

-- | A simple typechecker for the L3 language
-- It's very similar to the L1 typechecker
module Gibbon.L3.Typecheck
  ( tcProg, tcExp ) where


import Control.Monad.Except
import Data.Loc
import Text.PrettyPrint.GenericPretty
import qualified Data.Map as M
import qualified Data.List as L
import Prelude hiding (exp)

import Gibbon.Common
import Gibbon.L1.Typecheck hiding (tcProg, tcExp)
import Gibbon.L1.Syntax
import Gibbon.L3.Syntax

-- | Typecheck a L1 expression
--
tcExp :: (Out l, Eq l, FunctionTy (UrTy l)) =>
         Bool -> DDefs (UrTy l) -> Env2 (UrTy l) -> (L (PreExp E3Ext l (UrTy l))) ->
         TcM (UrTy l) (L (PreExp E3Ext l (UrTy l)))
tcExp isPacked ddfs env exp@(L p ex) =
  case ex of
    Ext ext ->
      case ext of
        -- One cursor in, (int, cursor') out
        ReadInt v -> do
          vty <- lookupVar env v exp
          ensureEqualTy exp vty CursorTy
          return $ ProdTy [IntTy, CursorTy]

        -- Write int at cursor, and return a cursor
        WriteInt v rhs -> do
          vty  <- lookupVar env v exp
          ensureEqualTy exp vty CursorTy
          vrhs <- go rhs
          ensureEqualTy exp vrhs IntTy
          return CursorTy

        -- Add a constant offset to a cursor variable
        AddCursor v rhs -> do
          vty  <- lookupVar env v exp
          ensureEqualTy exp vty CursorTy
          vrhs <- go rhs
          ensureEqualTy exp vrhs IntTy
          return CursorTy

        -- One cursor in, (tag,cursor) out
        -- QUESTION: what should be the type of the tag ?  It's just an Int for now
        ReadTag v -> do
          vty  <- lookupVar env v exp
          ensureEqualTy exp vty CursorTy
          return $ ProdTy [IntTy, CursorTy]

        -- Write Tag at Cursor, and return a cursor
        WriteTag _dcon v -> do
          vty  <- lookupVar env v exp
          ensureEqualTy exp vty CursorTy
          return CursorTy

        -- Create a new buffer, and return a cursor
        NewBuffer{} -> return CursorTy

        -- Create a scoped buffer, and return a cursor
        ScopedBuffer{} -> return CursorTy

        InitSizeOfBuffer{} -> return IntTy

        MMapFileSize{} -> return IntTy

        -- Takes in start and end cursors, and returns an Int
        SizeOfPacked start end -> do
          sty  <- lookupVar env start exp
          ensureEqualTy exp sty CursorTy
          ety  <- lookupVar env end exp
          ensureEqualTy exp ety CursorTy
          return IntTy

        -- Takes in a variable, and returns an Int
        SizeOfScalar v -> do
          sty <- lookupVar env v exp
          -- ASSUMPTION: Int is the only scalar value right now
          ensureEqualTy exp sty IntTy
          return IntTy

        -- The IntTy is just a placeholder. BoundsCheck is a side-effect
        BoundsCheck _ bound cur -> do
          rty <- lookupVar env bound exp
          ensureEqualTy exp rty CursorTy
          cty <- lookupVar env cur exp
          ensureEqualTy exp cty CursorTy
          return IntTy

        ReadCursor v -> do
          vty <- lookupVar env v exp
          ensureEqualTy exp vty CursorTy
          return $ ProdTy [CursorTy, CursorTy]

        WriteCursor cur val -> do
          curty  <- lookupVar env cur exp
          ensureEqualTy exp curty CursorTy
          valty <- go val
          ensureEqualTy exp valty CursorTy
          return CursorTy

        BumpRefCount end_r1 end_r2 -> do
          end_r1_ty  <- lookupVar env end_r1 exp
          ensureEqualTy exp end_r1_ty CursorTy
          end_r2_ty  <- lookupVar env end_r2 exp
          ensureEqualTy exp end_r2_ty CursorTy
          return IntTy

    -- All the other cases are exactly same as L1.Typecheck

    VarE v    -> lookupVar env v exp
    LitE _    -> return IntTy
    LitSymE _ -> return IntTy

    AppE v locs e -> do
      let funty =
            case (M.lookup v (fEnv env)) of
              Just ty -> ty
              Nothing -> error $ "Function not found: " ++ sdoc v ++ " while checking " ++
                                 sdoc exp ++ " at " ++ show p

      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp

      -- Check argument type
      argTy <- go e
      _     <- ensureEqualTy exp (inTy funty) argTy
      return (outTy funty)

    PrimAppE pr es -> do
      let len0 = checkLen exp pr 0 es
          len2 = checkLen exp pr 2 es
          len3 = checkLen exp pr 3 es

      tys <- mapM go es
      case pr of
        _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP]  -> do
          len2
          _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
          return IntTy

        _ | pr `elem` [MkTrue, MkFalse] -> do
          len0
          return BoolTy

        EqSymP -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return BoolTy

        _ | pr `elem` [EqIntP, LtP, GtP, LtEqP, GtEqP] -> do
          len2
          _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
          return BoolTy

        _ | pr `elem` [OrP, AndP] -> do
          len2
          _ <- ensureEqualTy (es !! 0) BoolTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) BoolTy (tys !! 1)
          return BoolTy

        RandP -> return IntTy

        SizeParam -> do
          len0
          return IntTy

        SymAppend -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
          return SymTy

        DictEmptyP ty -> do
          len0
          return $ SymDictTy ty

        DictInsertP ty -> do
          len3
          let [d,k,v] = tys
          _ <- ensureEqualTy exp (SymDictTy ty) d
          _ <- ensureEqualTy exp SymTy k
          _ <- ensureEqualTy exp ty v
          return d

        DictLookupP ty -> do
          len2
          let [d,k] = tys
          _ <- ensureEqualTy exp (SymDictTy ty) d
          _ <- ensureEqualTy exp SymTy k
          return ty

        DictHasKeyP ty -> do
          len2
          let [d,k] = tys
          _ <- ensureEqualTy exp (SymDictTy ty) d
          _ <- ensureEqualTy exp SymTy k
          return BoolTy

        ErrorP _str ty -> do
          len2
          return ty

        ReadPackedFile _fp _tycon _reg ty -> do
          len0
          if isPacked
          then return CursorTy
          else return ty

        PEndOf -> error "Do not use PEndOf after L2."

        oth -> error $ "L3.tcExp : PrimAppE : TODO " ++ sdoc oth

    LetE (v,locs,ty,rhs) e -> do
      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp
      -- Check RHS
      tyRhs <- go rhs
      _ <- ensureEqualTy exp tyRhs ty
      let env' = extendEnv env [(v,ty)]
      -- Check body
      tcExp isPacked ddfs env' e

    IfE tst consq alt -> do
      -- Check if the test is a boolean
      tyTst <- go tst
      _ <- ensureEqualTy exp tyTst BoolTy

      -- Check if both branches match
      tyConsq <- go consq
      tyAlt   <- go alt

      -- _ <- ensureEqualTy exp tyConsq tyAlt
      if tyConsq == tyAlt
      then return tyConsq
      else throwError $ GenericTC ("If branches have mismatched types:"
                                   ++ sdoc tyConsq ++ ", " ++ sdoc tyAlt) exp


    MkProdE es -> do
      tys <- mapM go es
      return $ ProdTy tys

    ProjE (i,_) e -> do
      ty  <- go e
      tyi <- tcProj exp i ty
      return tyi

    CaseE e cs -> do
      tye  <- go e
      let tycons = L.map (getTyOfDataCon ddfs . (\(a,_,_) -> a)) cs
      case L.nub tycons of
        [_one] -> do
          when (tye /= CursorTy && not (isPackedTy tye)) $
            throwError $ GenericTC ("Case scrutinee should be packed, or have a cursor type. Got"
                                    ++ sdoc tye) e
          tcCases isPacked ddfs env cs
        oth   -> throwError $ GenericTC ("Case branches have mismatched types: " ++ sdoc oth
                                         ++" , in " ++ sdoc exp) exp

    DataConE loc dc es -> do
      tys <- mapM go es
      let dcTy = getTyOfDataCon ddfs dc
          args = lookupDataCon ddfs dc
      if length args /= length es
      then throwError $ GenericTC ("Invalid argument length: " ++ sdoc es) exp
      else do
        -- Check if arguments match with expected datacon types
        sequence_ [ ensureEqualTy e ty1 ty2
                  | (ty1,ty2,e) <- zip3 args tys es]
        return $ PackedTy dcTy loc

    TimeIt e _ty _b -> do
      -- Before flatten, _ty is always (PackedTy "DUMMY_TY" ())
      -- enforce ty == _ty in strict mode ?
      ty <- go e
      return ty

    ParE a b -> do
      aty <- go a
      bty <- go b
      return (ProdTy [aty, bty])

    MapE{}  -> throwError $ UnsupportedExpTC exp
    FoldE{} -> throwError $ UnsupportedExpTC exp

    -- oth -> error $ "L1.tcExp : TODO " ++ sdoc oth

  where
    go = tcExp isPacked ddfs env


-- | Typecheck a L1 program
--
tcProg :: Bool -> Prog3 -> PassM Prog3
tcProg isPacked prg@Prog{ddefs,fundefs,mainExp} = do

  -- Handle functions
  mapM_ fd $ M.elems fundefs

  -- Handle main expression
  -- We don't change the type of mainExp to have cursors. So if it's type was `Packed`,
  -- it's still Packed, while the expression actually has type CursorTy.
  -- They're essentially the same.
  case mainExp of
    Nothing -> return ()
    Just (e,ty)  ->
      let res = runExcept $ tcExp isPacked ddefs env e
      in case res of
        Left err -> error $ sdoc err
        Right ty' -> if tyEq ty ty'
                     then return ()
                     else error $ "Expected type " ++ sdoc ty ++ "and got type " ++ sdoc ty'

  -- Identity function for now.
  return prg

  where
    env = progToEnv prg
    tyEq ty1 ty2 =
      case ty1 of
        PackedTy{}  -> ty2 == ProdTy [CursorTy,CursorTy] || ty1 == ty2
        ProdTy tys2 -> let ProdTy tys1 = ty1
                       in  all (\(a,b) -> tyEq a b) (zip tys1 tys2)
        _ -> ty1 == ty2

    -- fd :: forall e l . FunDef Ty1 Exp -> PassM ()
    fd FunDef{funArg,funTy,funBody} = do
      let env' = Env2 (M.singleton funArg inT) (fEnv env)
          res = runExcept $ tcExp isPacked ddefs env' funBody
          (inT, outT) = funTy
      case res of
        Left err -> error $ sdoc err
        Right ty -> if ty == outT
                    then return ()
                    else error $ "Expected type " ++ (sdoc outT)
                         ++ " and got type " ++ (sdoc ty)

      return ()


tcCases :: (Eq l, Out l, FunctionTy (UrTy l)) => Bool -> DDefs (UrTy l) -> Env2 (UrTy l) ->
           [(DataCon, [(Var, l)], L (PreExp E3Ext l (UrTy l)))] ->
           TcM (UrTy l) (L (PreExp E3Ext l (UrTy l)))
tcCases isPacked ddfs env cs = do
  tys <- forM cs $ \(c,args',rhs) -> do
           let args  = L.map fst args'
               targs = lookupDataCon ddfs c
               env'  = extendEnv env (zip args targs)
           tcExp isPacked ddfs env' rhs
  foldM_ (\acc (ex,ty) ->
            if ty == acc
            then return acc
            else throwError $ GenericTC ("Case branches have mismatched types: "
                                         ++ sdoc acc ++ ", " ++ sdoc ty) ex)
         (head tys) (zipWith (\ty (_,_,ex) -> (ex,ty)) tys cs)
  return $ head tys
