{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | An intermediate language which makes cursors explicit

module Gibbon.L3.Syntax
  (
    -- * Extended language
    E3Ext(..), Prog3, FunDef3, FunDefs3 , Exp3, Ty3

    -- * Functions
  , eraseLocMarkers, mapMExprs, cursorizeTy, toL3Prim

  , module Gibbon.Language
  )
where

import Control.DeepSeq
import Data.Loc
import Data.Map as M
import Data.Set as S
import Data.List as L
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.Language
import qualified Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

type Prog3 = Prog (L Exp3)

type FunDefs3 = FunDefs (L Exp3)

type FunDef3 = FunDef (L Exp3)

-- GHC uses the instance defined for L1.Ty1
-- instance FunctionTy Ty3 where

type Exp3 = PreExp E3Ext () Ty3

type Ty3 = UrTy ()

--------------------------------------------------------------------------------

-- | The extension that turns L1 into L3.
data E3Ext loc dec =
    ReadInt   Var                  -- ^ One cursor in, (int, cursor') out
  | WriteInt  Var (L (PreExp E3Ext loc dec)) -- ^ Write int at cursor, and return a cursor
  | AddCursor Var (L (PreExp E3Ext loc dec)) -- ^ Add a constant offset to a cursor variable
  | ReadTag   Var                  -- ^ One cursor in, (tag,cursor) out
  | WriteTag  DataCon Var          -- ^ Write Tag at Cursor, and return a cursor
  | NewBuffer L2.Multiplicity         -- ^ Create a new buffer, and return a cursor
  | ScopedBuffer L2.Multiplicity      -- ^ Create a temporary scoped buffer, and return a cursor
  | InitSizeOfBuffer L2.Multiplicity  -- ^ Returns the initial buffer size for a specific multiplicity
  | MMapFileSize Var
  | SizeOfPacked Var Var           -- ^ Takes in start and end cursors, and returns an Int
                                   --   we'll probably represent (sizeof x) as (end_x - start_x) / INT
  | SizeOfScalar Var               -- ^ sizeof(var)
  | BoundsCheck Int Var Var        -- ^ Bytes required, region, write cursor
  | ReadCursor Var                 -- ^ Reads and returns the cursor at Var
  | WriteCursor Var (L (PreExp E3Ext loc dec)) -- ^ Write a cursor, and return a cursor
  | BumpRefCount Var Var           -- ^ Given an end-of-region ptr, bump it's refcount.
                                   --   Return the updated count (optional).
  deriving (Show, Ord, Eq, Read, Generic, NFData)

instance FreeVars (E3Ext l d) where
  gFreeVars  e =
    case e of
      ReadInt  v     -> S.singleton v
      WriteInt v ex  -> S.insert v (gFreeVars ex)
      AddCursor v ex -> S.insert v (gFreeVars ex)
      ReadTag v      -> S.singleton v
      WriteTag _ v   -> S.singleton v
      NewBuffer{}    -> S.empty
      ScopedBuffer{} -> S.empty
      InitSizeOfBuffer{} -> S.empty
      MMapFileSize v     -> S.singleton v
      SizeOfPacked c1 c2 -> S.fromList [c1, c2]
      SizeOfScalar v     -> S.singleton v
      BoundsCheck{}      -> S.empty
      ReadCursor v       -> S.singleton v
      WriteCursor c ex   -> S.insert c (gFreeVars ex)
      BumpRefCount r1 r2 -> S.fromList [r1, r2]

instance (Out l, Out d, Show l, Show d) => Expression (E3Ext l d) where
  type LocOf (E3Ext l d) = l
  type TyOf  (E3Ext l d) = UrTy l
  isTrivial _ = False

instance (Out l, Show l) => Typeable (E3Ext l (UrTy l)) where
    gRecoverType = error "L3.gRecoverType"

instance (Show l, Out l) => Flattenable (E3Ext l (UrTy l)) where
    gFlattenGatherBinds _ddfs _env ex = return ([], ex)
    gFlattenExp _ddfs _env ex = return ex

-----------------------------------------------------------------------------------------
-- Do this manually to get prettier formatting: (Issue #90)

instance (Out l, Out d) => Out (E3Ext l d)

-----------------------------------------------------------------------------------------

-- | Erase LocVar markers from the data definition
eraseLocMarkers :: DDef L2.Ty2 -> DDef Ty3
eraseLocMarkers (DDef tyargs tyname ls) = DDef tyargs tyname $ L.map go ls
  where go :: (DataCon,[(IsBoxed,L2.Ty2)]) -> (DataCon,[(IsBoxed,Ty3)])
        go (dcon,ls') = (dcon, L.map (\(b,ty) -> (b,L2.stripTyLocs ty)) ls')

cursorizeTy :: UrTy a -> UrTy b
cursorizeTy ty =
  case ty of
    IntTy     -> IntTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map cursorizeTy ls
    SymDictTy ty' -> SymDictTy $ cursorizeTy ty'
    PackedTy{}    -> ProdTy [CursorTy, CursorTy]
    ListTy ty'    -> ListTy $ cursorizeTy ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy

-- | Map exprs with an initial type environment:
-- Exactly the same function that was in L2 before
mapMExprs :: Monad m => (Env2 Ty3 -> L Exp3 -> m (L Exp3)) -> Prog3 -> m Prog3
mapMExprs fn (Prog ddfs fundefs mainExp) =
  Prog ddfs <$>
    (mapM (\f@FunDef{funArg,funTy,funBody} ->
              let env = Env2 (M.singleton funArg (fst funTy)) funEnv
              in do
                bod' <- fn env funBody
                return $ f { funBody =  bod' })
     fundefs)
    <*>
    (mapM (\ (e,t) -> (,t) <$> fn (Env2 M.empty funEnv) e) mainExp)
  where funEnv = M.map funTy fundefs

toL3Prim :: Prim L2.Ty2 -> Prim Ty3
toL3Prim pr = fmap L2.stripTyLocs pr
