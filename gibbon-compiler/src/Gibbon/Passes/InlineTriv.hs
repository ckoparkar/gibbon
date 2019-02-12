-- | Compiler pass to inline trivials.
module Gibbon.Passes.InlineTriv (inlineTriv, inlineTrivExp) where

import           Data.Loc
import qualified Data.Map as M
import           Prelude hiding (exp)
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.L1.Syntax


-- | Inline trivial let bindings (binding a var to a var or int), mainly to clean up
--   the output of `flatten`.
inlineTriv :: Prog1 -> PassM Prog1
inlineTriv p@(Prog ddefs funs main) =
    return (Prog ddefs (fmap inlineTrivFun funs) main')
  where
    env2 = progToEnv p
    inlineTrivFun (FunDef nam narg (targ, ty) bod) = do
      let env2' = extendVEnv narg targ env2
      FunDef nam narg (targ, ty) (inlineTrivExp ddefs env2' bod)
    main' = case main of
              Nothing -> Nothing
              Just (m,ty) -> Just (inlineTrivExp ddefs env2 m, ty)


type MyExp l = L (PreExp NoExt l (UrTy l))
type Env l = [(Var, (UrTy l, MyExp l))]

inlineTrivExp :: forall l. (Out l, Show l)
              => DDefs (TyOf (MyExp l)) -> Env2 (TyOf (MyExp l)) -> MyExp l -> MyExp l
inlineTrivExp ddefs env21 = go [] env21
  where

  -- Just a hook for debugging:
  go :: Env l -> Env2 (TyOf (MyExp l)) -> MyExp l -> MyExp l
  go env env2 e = exp env env2 e

  -- | Here we go to some lengths to maintain the syntactic invariants
  -- for the extended L2 forms. The idea is that we can only reference
  -- variables within these forms, but we still must apply the
  -- environment because the old bindings have been removed.
  --
  -- An alternative would be to let the extended forms disappear at
  -- this point, and handle them at the level of "AppE" in Lower.hs.
  _withVar :: Env l -> Var -> (Var -> MyExp l) -> MyExp l
  _withVar env v fn =
    case lookup v env of
      Nothing        -> fn v
      Just (_, (L _ (VarE v2))) -> fn v2
      -- fixme, need gensym:
      Just (ty,oth)  -> L NoLoc $ LetE (v,[],ty,oth) $ fn v

  exp :: Env l -> Env2 (TyOf (MyExp l)) -> MyExp l -> (MyExp l)
  exp env env2 (L p0 e0) = L p0 $
    case e0 of
      Ext _  -> e0
      VarE v -> case lookup v env of
                    Nothing -> VarE v
                    Just (_,e) -> unLoc e
      LitE i -> LitE i
      LitSymE v -> LitSymE v

      AppE v lvs e -> AppE v lvs $ go env env2 e
      PrimAppE p es -> PrimAppE p $ map (go env env2) es

      LetE (v,lvs,t,e') e ->
       case e' of
         L _ (VarE v') ->
           case lookup v' env of
             Nothing -> unLoc $ go ((v,(t,e')):env) (extendVEnv v t env2) e
             Just pr -> unLoc $ go ((v,pr):env) (extendVEnv v t env2) e
         et | isTrivial et ->
                -- Apply existing renames:
                let et' = go env env2 et in
                unLoc $ go ((v,(t,et')):env) (extendVEnv v t env2) e
         _ -> LetE (v,lvs,t,go env env2 e') (go env (extendVEnv v t env2) e)

      IfE e1 e2 e3 -> IfE (go env env2 e1) (go env env2 e2) (go env env2 e3)

      -- TODO: Type check here:
      -- FIXME CSK.
      ProjE (i,_) e -> unLoc $ mkProj i 100 $ go env env2 e

      MkProdE es -> MkProdE $ map (go env env2) es
      CaseE e mp ->
       let e' = go env env2 e
           mp' = map (\(c,args,ae) ->
                         let tys   = lookupDataCon ddefs c
                             vars  = map fst args
                             env2' = extendsVEnv (M.fromList (zip vars tys)) env2
                         in (c,args,go env env2' ae))
                     mp
       in CaseE e' mp'

      DataConE loc c es -> DataConE loc c $ map (go env env2) es
      TimeIt e t b -> TimeIt (go env env2 e) t b
      ParE a b -> ParE (go env env2 a) (go env env2 b)
      MapE (v,t,e') e -> MapE (v,t,go env env2 e') (go env env2 e)
      FoldE (v1,t1,e1) (v2,t2,e2) e3 ->
       FoldE (v1,t1,go env env2 e1) (v2,t2,go env env2 e2) (go env env2 e3)

      {-
      -- FIXME: Remove:
      L2.NewBuffer -> L2.NewBuffer
      L2.ReadInt v     -> unLoc $ withVar env v $ \v2 -> L NoLoc $ L2.ReadInt v2
      L2.WriteInt v e  -> unLoc $ withVar env v $ \v2 -> L NoLoc $
                                                         L2.WriteInt v2 (go env e)
      L2.AddCursor v i -> unLoc $ withVar env v $ \v2 -> L NoLoc $ L2.AddCursor v2 i

      p | L2.isExtendedPattern p ->
          internalError $ "InlineTriv: failed to handle extended L2 form: "
          ++ndoc p++", env: "++ndoc env
      -}

-- Helpers which do opportunistic reduction:

-- mkProj :: Int -> MyExp l -> MyExp l
-- mkProj ix (L _ (MkProdE ls)) = ls !! ix
-- mkProj ix e@(L p _) = L p $ ProjE ix e
