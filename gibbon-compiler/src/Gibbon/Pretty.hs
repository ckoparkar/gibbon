{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Gibbon.Pretty
  ( Pretty(..), PPStyle(..), render ) where

import           Prelude hiding ((<>))
import           Data.Loc
import           Text.PrettyPrint
import           Text.PrettyPrint.GenericPretty
import qualified Data.Map as M

import qualified Gibbon.L0.Syntax as L0
import           Gibbon.L1.Syntax
import           Gibbon.L2.Syntax as L2
import           Gibbon.L3.Syntax as L3
import           Gibbon.Common hiding (l)
import           Gibbon.HaskellFrontend ( primMap )
import qualified Gibbon.L4.Syntax as L4

--------------------------------------------------------------------------------

-- | Rendering style.
data PPStyle
    = PPHaskell  -- ^ Prefer compatibility with GHC over anything else.
    | PPInternal -- ^ Noisiest, useful for Gibbon developers.
    deriving (Ord, Eq, Show, Read)


class Pretty e where
    pprintWithStyle :: PPStyle -> e -> Doc

    pprint :: e -> Doc
    pprint = pprintWithStyle PPInternal

    {-# MINIMAL pprintWithStyle  #-}


doublecolon :: Doc
doublecolon = colon <> colon

--------------------------------------------------------------------------------

-- A convenience wrapper over some of the constraints.
type HasPretty ex = (Pretty ex, Pretty (TyOf ex), Pretty (ArrowTy (TyOf ex)))

-- Program:
instance HasPretty ex => Pretty (Prog ex) where
    pprintWithStyle sty (Prog ddefs funs me) =
        let meDoc = case me of
                      Nothing -> empty
                      Just (e,ty) -> renderMain (pprintWithStyle sty e) (pprintWithStyle sty ty)
            ddefsDoc = vcat $ map (pprintWithStyle sty) $ M.elems ddefs
            funsDoc = vcat $ map (pprintWithStyle sty) $ M.elems funs
        in case sty of
             PPInternal -> ddefsDoc $+$ funsDoc $+$ meDoc
             PPHaskell  -> ghc_compat_prefix $+$ ddefsDoc $+$ funsDoc $+$ meDoc $+$ ghc_compat_suffix
      where
        renderMain :: Doc -> Doc -> Doc
        renderMain m ty = text "gibbon_main" <+> doublecolon <+> ty
                            $$ text "gibbon_main" <+> equals $$ nest 4 m

        -- Things we need to make this a valid compilation unit for GHC:
        ghc_compat_prefix = text "{-# LANGUAGE ScopedTypeVariables #-}\n" $+$
                            text "module Main where\n" $+$
                            -- Need a better stub for 'TimeIt' in GHC.
                            text "timeit = id\n"
        ghc_compat_suffix = text "\nmain = print gibbon_main"

-- Functions:
instance HasPretty ex => Pretty (FunDef ex) where
    pprintWithStyle sty FunDef{funName,funArg,funTy,funBody} =
        text (fromVar funName) <+> doublecolon <+> pprintWithStyle sty funTy
          $$ renderBod <> text "\n"
      where
        renderBod :: Doc
        renderBod = text (fromVar funName) <+> text (fromVar funArg) <+> equals
                      $$ nest 4 (pprintWithStyle sty funBody)

-- Datatypes
instance Pretty ex => Pretty (DDef ex) where
    pprintWithStyle sty DDef{tyName,tyArgs,dataCons} =
        text "data" <+> pprintWithStyle sty tyName <+> hsep (map (pprintWithStyle sty) tyArgs)
          <+> equals <+> vcat (punctuate " | " $
                                 map (\(d,args) ->
                                        text d <+> hsep (map (\(_,b) -> pprintWithStyle sty b) args))
                                   dataCons)
          <+> (if sty == PPHaskell
               then text "\n  deriving Show \n"
               else empty)


-- Primitives
instance Ord d => Pretty (Prim d) where
    pprintWithStyle _ pr =
        -- We add PEndOf here because it's not exposed to the users, and as a result,
        -- is not defined as a primop in the parser primMap.
        -- TODO: Dictionaries!!!
        let renderPrim = M.union (M.singleton PEndOf "pendof") $
                         M.fromList (map (\(a,b) -> (b,a)) (M.toList primMap))
        in case M.lookup pr renderPrim of
              Nothing  -> error $ "pprint: Unknown primitive: " ++ render (pprint pr)
              Just str -> text str


-- Types:
instance Pretty () where
    pprintWithStyle _ _ = empty

instance Pretty Var where
    pprintWithStyle _ v = text (fromVar v)

instance Pretty TyVar where
    pprintWithStyle sty tyvar =
      case sty of
        PPHaskell -> case tyvar of
                       BoundTv v  -> text $ fromVar v
                       SkolemTv{} -> doc tyvar
                       UserTv v   -> text $ fromVar v
        PPInternal -> doc tyvar

instance (Pretty l) => Pretty (UrTy l) where
    pprintWithStyle sty ty =
        case ty of
          IntTy  -> text "Int"
          BoolTy -> text "Bool"
          ProdTy tys    -> parens $ hcat $ punctuate "," $ map (pprintWithStyle sty) tys
          SymDictTy ty1 -> text "Dict" <+> pprintWithStyle sty ty1
          PackedTy tc l ->
              case sty of
                PPHaskell  -> text tc
                PPInternal -> text "Packed" <+> text tc <+> pprintWithStyle sty l
          ListTy ty1 -> text "List" <+> pprintWithStyle sty ty1
          PtrTy     -> text "Ptr"
          CursorTy  -> text "Cursor"

-- Function type for L1 and L3
instance Pretty (UrTy (), UrTy ()) where
    pprintWithStyle sty (a,b) = pprintWithStyle sty a <+> text "->" <+> pprintWithStyle sty b

instance Pretty ArrowTy2 where
    -- TODO: start metadata at column 0 instead of aligning it with the type
    pprintWithStyle sty fnty =
        case sty of
          PPHaskell ->
            pprintWithStyle sty (arrIn fnty) <+> text "->" <+> pprintWithStyle sty (arrOut fnty)
          PPInternal ->
            pprintWithStyle PPHaskell fnty $$
              braces (text "locvars" <+> doc (locVars fnty) <> comma $$
                      text "effs: " <+> doc (arrEffs fnty) <> comma $$
                      text "locrets: " <+> doc (locRets fnty))


-- Expressions

instance Pretty (PreExp e l d) => Pretty (L (PreExp e l d)) where
    pprintWithStyle sty (L _ e) = pprintWithStyle sty e

-- CSK: Needs a better name.
type HasPrettyToo e l d = (Ord d, Eq d, Pretty d, Pretty l, Pretty (e l d), TyOf (e l (UrTy l)) ~ TyOf (PreExp e l (UrTy l)))

instance HasPrettyToo e l d => Pretty (PreExp e l d) where
    pprintWithStyle sty ex0 =
        case ex0 of
          VarE v -> pprintWithStyle sty v
          LitE i -> int i
          LitSymE v -> pprintWithStyle sty v
          AppE v ls e -> pprintWithStyle sty v <+>
                         (if null ls
                          then empty
                          else brackets $ hcat (punctuate "," (map pprint ls))) <+>
                         (pprintWithStyle sty e)
          PrimAppE pr es ->
              case pr of
                  _ | pr `elem` [AddP, SubP, MulP, DivP, ModP, ExpP, EqSymP, EqIntP, LtP, GtP, SymAppend] ->
                      let [a1,a2] = es
                      in pprintWithStyle sty a1 <+> pprintWithStyle sty pr <+> pprintWithStyle sty a2

                  _ | pr `elem` [MkTrue, MkFalse, SizeParam] -> pprintWithStyle sty pr

                  _ -> pprintWithStyle sty pr <> parens (hsep $ map (pprintWithStyle sty) es)

          LetE (v,ls,ty,e1) e2 -> (text "let") <+>
                                  pprintWithStyle sty v <+> doublecolon <+>
                                  (if null ls
                                   then empty
                                   else brackets (hcat (punctuate comma (map (pprintWithStyle sty) ls)))) <+>
                                  pprintWithStyle sty ty <+>
                                  equals <+>
                                  pprintWithStyle sty e1 <+>
                                  text "in" $+$
                                  pprintWithStyle sty e2
          IfE e1 e2 e3 -> text "if" <+>
                          pprintWithStyle sty e1 $+$
                          text "then" <+>
                          pprintWithStyle sty e2 $+$
                          text "else" <+>
                          pprintWithStyle sty e3
          MkProdE es -> lparen <> hcat (punctuate (text ", ") (map (pprintWithStyle sty) es)) <> rparen
          ProjE (i,_) e ->
              let edoc = pprintWithStyle sty e
              in case sty of
                PPInternal ->  text "#" <> int i <+> edoc
                PPHaskell  ->
                    case i of
                      0 -> text "fst" <+> edoc
                      1 -> text "snd" <+> edoc
                      _ -> error (render $ pprintWithStyle PPInternal ex0) -- text "#" <> int i <+> edoc
          CaseE e bnds -> text "case" <+> pprintWithStyle sty e <+> text "of" $+$
                          nest 4 (vcat $ map dobinds bnds)
          DataConE l dc es -> text dc <+>
                              (if isEmpty (pprintWithStyle sty l)
                               then empty
                               else pprintWithStyle sty l) <+>
                              hsep (map (pprintWithStyle sty) es)
                              -- lparen <> hcat (punctuate (text ",") (map (pprintWithStyle sty) es)) <> rparen
          TimeIt e _ty _b -> text "timeit" <+> parens (pprintWithStyle sty e)
          ParE a b -> pprintWithStyle sty a <+> text "||" <+> pprintWithStyle sty b
          Ext ext -> pprintWithStyle sty ext
          MapE{} -> error $ "Unexpected form in program: MapE"
          FoldE{} -> error $ "Unexpected form in program: FoldE"
        where
          dobinds (dc,vls,e) = text dc <+> hcat (punctuate (text " ")
                                                           (map (\(v,l) -> if isEmpty (pprintWithStyle sty l)
                                                                           then pprintWithStyle sty v
                                                                           else pprintWithStyle sty v <> doublecolon <> pprintWithStyle sty l)
                                                            vls))
                               <+> text "->" $+$ nest 4 (pprintWithStyle sty e)
-- L1
instance Pretty (NoExt l d) where
    pprintWithStyle _ _ = empty

-- L2
instance Pretty l => Pretty (L2.PreLocExp l) where
    pprintWithStyle _ le =
        case le of
          StartOfLE r -> lparen <> text "startof" <+> text (show r) <> rparen
          AfterConstantLE i l -> lparen <> pprint l <+> text "+" <+> int i <> rparen
          AfterVariableLE v l -> lparen <> pprint l <+> text "+" <+> doc v <> rparen
          InRegionLE r -> lparen <> text "inregion" <+> text (show r) <> rparen
          FromEndLE l -> lparen <> text "fromend" <+> pprint l <> rparen

instance HasPrettyToo E2Ext l (UrTy l) => Pretty (L2.E2Ext l (UrTy l)) where
    pprintWithStyle _ ex0 =
        case ex0 of
          LetRegionE r e -> text "letregion" <+>
                               doc r <+> text "in" $+$ pprint e
          LetLocE l le e -> text "letloc" <+>
                               pprint l <+> equals <+> pprint le <+> text "in" $+$ pprint e
          RetE ls v -> text "return" <+>
                          lbrack <> hcat (punctuate (text ",") (map pprint ls)) <> rbrack <+>
                          doc v
          FromEndE l -> text "fromend" <+> pprint l
          L2.BoundsCheck i l1 l2 -> text "boundscheck" <+> int i <+> pprint l1 <+> pprint l2
          IndirectionE tc dc (l1,v1) (l2,v2) e -> text "indirection" <+>
                                                     doc tc <+>
                                                     doc dc <+>
                                                     lparen <>
                                                     hcat (punctuate (text ",") [pprint l1,text (fromVar v1)]) <>
                                                     rparen <+>
                                                     lparen <>
                                                     hcat (punctuate (text ",") [pprint l2,text (fromVar v2)]) <>
                                                     rparen <+>
                                                     pprint e

-- L3
instance (Out l) => Pretty (L3.E3Ext l (UrTy l)) where
    pprintWithStyle _ = doc -- TODO: replace this with actual pretty printing for L3 forms

-- L4
instance Pretty L4.Prog where
   pprintWithStyle _ = doc -- TODO: replace this with actual pretty printing for L4 forms

--------------------------------------------------------------------------------

-- All other generic PreExp things are defined over (PreExp e l (UrTy l)), so
-- we have to redefine them for L0 (which uses Ty0 instead of UrTy).

instance Pretty L0.Ty0 where
  pprintWithStyle _ ty =
      case ty of
        L0.IntTy      -> text "Int"
        L0.BoolTy     -> text "Bool"
        L0.TyVar v    -> doc v
        L0.MetaTv v   -> doc v
        L0.ProdTy tys -> parens $ hcat $ punctuate "," $ map pprint tys
        L0.SymDictTy ty1 -> text "Dict" <+> pprint ty1
        L0.ArrowTy a b   -> pprint a <+> text "->" <+> pprint b
        L0.PackedTy tc l -> text "Packed" <+> text tc <+> brackets (hcat (map pprint l))
        L0.ListTy ty1 -> brackets (pprint ty1)

instance Pretty L0.TyScheme where
  pprintWithStyle _ (L0.ForAll tvs ty) = text "forall" <+> hsep (map doc tvs) <+> text "." <+> pprint ty

instance Pretty (L0.E0Ext () L0.Ty0) where
  pprintWithStyle _ ex0 =
    case ex0 of
      L0.LambdaE (v,ty) bod -> parens (text "\\" <+> doc v <+> doublecolon <+> pprint ty <+> text " -> "
                                         $$ nest 4 (pprint bod))
      L0.PolyAppE{} -> doc ex0
