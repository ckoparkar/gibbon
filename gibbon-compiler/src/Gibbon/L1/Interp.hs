{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Interpreter for the source language (L1)
--

module Gibbon.L1.Interp
    ( execAndPrint, interpProg1,
      -- * Helpers
      applyPrim, strToInt
    ) where

import           Data.ByteString.Builder (toLazyByteString, string8)
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Writer
import           Control.Monad.State
import           Data.List as L
import           Data.Loc
import           Data.Map as M
import           System.Clock
import           System.IO.Unsafe
import           System.Random
import           Text.PrettyPrint.GenericPretty
import qualified Data.ByteString.Lazy.Char8 as B

import           Gibbon.Common
import           Gibbon.Interp
import           Gibbon.L1.Syntax as L1


-- TODO:
-- It's a SUPERSET, but use the Value type from TargetInterp anyway:
-- Actually, we should merge these into one type with a simple extension story.
-- import Gibbon.TargetInterp (Val(..), applyPrim)

interpChatter :: Int
interpChatter = 7

------------------------------------------------------------

instance Interp Prog1 where
  interpProg = interpProg1

-- | Interpret a program, including printing timings to the screen.
--   The returned bytestring contains that printed timing info.
interpProg1 :: RunConfig -> Prog1 -> IO (Value, B.ByteString)
interpProg1 rc Prog{ddefs,fundefs,mainExp} =
  case mainExp of
    -- Print nothing, return "void"
    Nothing -> return (VProd [], B.empty)
    Just (e,_) -> do
      let fenv = M.fromList [ (funName f , f) | f <- M.elems fundefs]
      -- logs contains print side effects
      ((res,logs),Store _finstore) <-
         runStateT (runWriterT (interp rc ddefs fenv e)) (Store M.empty)
      return (res, toLazyByteString logs)


interp :: forall l e. ( Out l, Show l, Expression (e l (UrTy l)) )
       => RunConfig
       -> DDefs (TyOf (L (PreExp e l (UrTy l))))
       -> M.Map Var (FunDef (L (PreExp e l (UrTy l))))
       -> L (PreExp e l (UrTy l))
       -> WriterT Log (StateT Store IO) Value
interp rc _ddefs fenv = go M.empty
  where
    {-# NOINLINE goWrapper #-}
    goWrapper !_ix env ex = go env ex

    go :: ValEnv -> L (PreExp e l (UrTy l)) -> WriterT Log (StateT Store IO) Value
    go env (L _ x0) =
        case x0 of
          Ext{} -> error "Cannot interpret NoExt"

          LitE c    -> return $ VInt c
          LitSymE s -> return $ VInt (strToInt $ fromVar s)
          VarE v    -> return $ env # v

          PrimAppE p ls   -> do args <- mapM (go env) ls
                                return $ applyPrim rc p args
          ProjE (ix,_) ex -> do VProd ls <- go env ex
                                return $ ls !! ix

          AppE f _ b ->  do rand <- go env b
                            case M.lookup f fenv of
                             Just fn -> go (M.insert (funArg fn) rand env) (funBody fn)
                             Nothing -> error $ "L1.Interp: unbound function in application: "++ndoc x0

          CaseE _ [] -> error$ "L1.Interp: CaseE with empty alternatives list: "++ndoc x0

          CaseE x1 alts@((_sometag,_,_):_) -> do
                 v <- go env x1
                 case v of
{-
                   VCursor idx off | rcCursors rc ->
                      do Store store <- get
                         let Buffer seq1 = store IM.! idx
                         case S.viewl (S.drop off seq1) of
                           S.EmptyL -> error "L1.Interp: case scrutinize on empty/out-of-bounds cursor."
                           SerTag tg _ :< _rst -> do
                             let tycon = getTyOfDataCon ddefs sometag
                                 datacon = (getConOrdering ddefs tycon) !! fromIntegral tg
                             let (_tagsym,[(curname,_)],rhs) = lookup3 datacon alts
                                 -- At this ^ point, we assume that a pattern match against a cursor binds ONE value.
                             let env' = M.insert curname (VCursor idx (off+1)) env
                             go env' rhs
                           oth :< _ -> error $ "L1.Interp: expected to read tag from scrutinee cursor, found: "++show oth
-}

                   VPacked k ls2 ->
                       let vs = L.map fst prs
                           (_,prs,rhs) = lookup3 k alts
                           env' = M.union (M.fromList (zip vs ls2)) env
                       in go env' rhs
                   _ -> error$ "L1.Interp: type error, expected data constructor, got: "++ndoc v++
                               "\nWhen evaluating scrutinee of case expression: "++ndoc x1


          LetE (v,_,_ty,rhs) bod -> do
            rhs' <- go env rhs
            let env' = M.insert v rhs' env
            go env' bod

          MkProdE ls -> VProd <$> mapM (go env) ls
          -- TODO: Should check this against the ddefs.
          DataConE _ k ls -> do
              args <- mapM (go env) ls
              return $ VPacked k args
{-
              -- Constructors are overloaded.  They have different behavior depending on
              -- whether we are AFTER Cursorize or not.
              case args of
                [ VCursor idx off ] | rcCursors rc ->
                    do Store store <- get
                       let tag       = SerTag (getTagOfDataCon ddefs k) k
                           store'    = IM.alter (\(Just (Buffer s1)) -> Just (Buffer $ s1 |> tag)) idx store
                       put (Store store')
                       return $ VCursor idx (off+1)
                _ -> return $ VPacked k args
-}

          TimeIt bod _ isIter -> do
              let iters = if isIter then rcIters rc else 1
              !_ <- return $! force env
              st <- liftIO $ getTime clk
              val <- foldM (\ _ i -> goWrapper i env bod)
                            (error "Internal error: this should be unused.")
                         [1..iters]
              en <- liftIO $ getTime clk
              let tm = fromIntegral (toNanoSecs $ diffTimeSpec en st)
                        / 10e9 :: Double
              if isIter
               then do tell$ string8 $ "ITERS: "++show iters       ++"\n"
                       tell$ string8 $ "SIZE: " ++show (rcSize rc) ++"\n"
                       tell$ string8 $ "BATCHTIME: "++show tm      ++"\n"
               else tell$ string8 $ "SELFTIMED: "++show tm ++"\n"
              return $! val

          ParE a b -> do
            a' <- go env a
            b' <- go env b
            return $ VProd [a', b']

          IfE a b c -> do v <- go env a
                          case v of
                           VBool flg -> if flg
                                        then go env b
                                        else go env c
                           oth -> error$ "interp: expected bool, got: "++show oth

          MapE _ _bod    -> error "L1.Interp: finish MapE"
          FoldE _ _ _bod -> error "L1.Interp: finish FoldE"

applyPrim :: (Show l) => RunConfig -> Prim (UrTy l) -> [Value] -> Value
applyPrim rc p ls =
 case (p,ls) of
   (MkTrue,[])             -> VBool True
   (MkFalse,[])            -> VBool False
   (AddP,[VInt x, VInt y]) -> VInt (x+y)
   (SubP,[VInt x, VInt y]) -> VInt (x-y)
   (MulP,[VInt x, VInt y]) -> VInt (x*y)
   (DivP,[VInt x, VInt y]) -> VInt (x `quot` y)
   (ModP,[VInt x, VInt y]) -> VInt (x `rem` y)
   (ExpP,[VInt x, VInt y]) -> VInt (x ^ y)
   -- Constrained to the value of RAND_MAX (in C) on my laptop: 2147483647 (2^31 − 1)
   (RandP,[]) -> VInt $ (unsafePerformIO randomIO) `mod` 2147483647
   (SymAppend,[VInt x, VInt y]) -> VInt (x * (strToInt $ show y))
   (EqSymP,[VInt x, VInt y]) -> VBool (x==y)
   (EqIntP,[VInt x, VInt y]) -> VBool (x==y)
   (LtP,[VInt x, VInt y]) -> VBool (x < y)
   (GtP,[VInt x, VInt y]) -> VBool (x > y)
   (LtEqP,[VInt x, VInt y]) -> VBool (x <= y)
   (GtEqP,[VInt x, VInt y]) -> VBool (x >= y)
   (AndP, [VBool x, VBool y]) -> VBool (x && y)
   (OrP, [VBool x, VBool y])  -> VBool (x || y)
   ((DictInsertP _ty),[VDict mp, key, val]) -> VDict (M.insert key val mp)
   ((DictLookupP _),[VDict mp, key])        -> mp # key
   ((DictHasKeyP _),[VDict mp, key])        -> VBool (M.member key mp)
   ((DictEmptyP _),[])                      -> VDict M.empty
   ((ErrorP msg _ty),[]) -> error msg
   (SizeParam,[]) -> VInt (rcSize rc)
   (ReadPackedFile file _ _ ty,[]) ->
       error $ "L1.Interp: unfinished, need to read a packed file: "++show (file,ty)
   oth -> error $ "unhandled prim or wrong number of arguments: "++show oth


clk :: Clock
clk = Monotonic
