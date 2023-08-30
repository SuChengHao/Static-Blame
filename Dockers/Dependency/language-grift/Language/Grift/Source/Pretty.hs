{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Source.Pretty where

import           Prelude hiding ((<>))

import           Text.PrettyPrint

import           Language.Grift.Common.Syntax
import           Language.Grift.Common.Pretty
import           Language.Grift.Source.Syntax

pparg :: Name -> Ann a Type -> Doc
pparg a (Ann _ BlankTy) = ppe a
pparg a t               = lbrack <> ppe a <+> char ':' <+> ppe t <> rbrack

instance (Pretty e, Show a) => Pretty (BindF (Ann a Type) e) where
  ppe (Bind x (Ann _ BlankTy) e) = brackets (text x $+$ indent (ppe e))
  ppe (Bind x t e)               =
    brackets (text x <+> char ':' <+> ppe t $+$ indent (ppe e))

instance (Pretty e, Show a) => Pretty (ExpF (Ann a Type) e) where
  ppe (Op op es)                 = parens $ ppe op <+> hsep (map ppe es)
  ppe (If e1 e2 e3)              = parens $ text "if" <+> ppe e1 $+$ indent (ppe e2) $+$ indent (ppe e3)
  ppe (Cond es)                  = parens $ text "cond" $+$ vcat' (map (\(cond, e) -> brackets $ ppe cond $+$ ppe e) es)
  ppe (App e1 es)                = parens $ ppe e1 <+> hsep (map ppe es)
  ppe (Lam xs e (Ann _ (ArrTy ts (Ann _ t))))    =
    parens (text "lambda" <+> parens
            (vcat' (zipWith pparg xs ts)) <+>
            (case t of
               BlankTy -> empty
               _       -> char ':' <+> ppe t)
            $+$ indent (ppe e))
  ppe (Lam _ _ t)                = error ("defined as lambda but has type" ++ show t)
  ppe (DConst x (Ann _ t) e)     = parens $ text "define" <+> text x <+>
    (case t of
        BlankTy -> ppe e
        _       -> char ':' <+> ppe t <+> ppe e)
  ppe (DLam x xs e (Ann _ (ArrTy ts (Ann _ t)))) = parens $ text "define" <+>
    parens (text x <+> vcat' (zipWith pparg xs ts)) <+>
    (case t of
       BlankTy -> empty
       _       -> char ':' <+> ppe t)
    $+$ indent (ppe e)
  ppe (DLam x _ _ (Ann _ t))     = error (x ++ " is defined as lambda but has type: " ++ show t)
  ppe (Ref e)                    = parens $ text "box" <+> ppe e
  ppe (DeRef e)                  = parens $ text "unbox" <+> ppe e
  ppe (Assign e1 e2)             = parens $ text "box-set!" <+> ppe e1 <+> ppe e2
  ppe (GRef e)                   = parens $ text "gbox" <+> ppe e
  ppe (GDeRef e)                 = parens $ text "gunbox" <+> ppe e
  ppe (GAssign e1 e2)            = parens $ text "gbox-set!" <+> ppe e1 <+> ppe e2
  ppe (MRef e)                   = parens $ text "mbox" <+> ppe e
  ppe (MDeRef e)                 = parens $ text "munbox" <+> ppe e
  ppe (MAssign e1 e2)            = parens $ text "mbox-set!" <+> ppe e1 <+> ppe e2
  ppe (Vect e1 e2)               = parens $ text "vector" <+> ppe e1 <+> ppe e2
  ppe (VectRef e1 e2)            = parens $ text "vector-ref" <+> ppe e1 <+> ppe e2
  ppe (VectSet e1 e2 e3)         = parens $ text "vector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (GVect e1 e2)              = parens $ text "gvector" <+> ppe e1 <+> ppe e2
  ppe (GVectRef e1 e2)           = parens $ text "gvector-ref" <+> ppe e1 <+> ppe e2
  ppe (GVectSet e1 e2 e3)        = parens $ text "gvector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (MVect e1 e2)              = parens $ text "mvector" <+> ppe e1 <+> ppe e2
  ppe (MVectRef e1 e2)           = parens $ text "mvector-ref" <+> ppe e1 <+> ppe e2
  ppe (MVectSet e1 e2 e3)        = parens $ text "mvector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (Tuple es)                 = parens $ text "tuple" <+> hsep (map ppe es)
  ppe (TupleProj e i)            = parens $ text "tuple-proj" <+> ppe e <+> int i
  ppe (Let bs es)                = parens $ text "let" <+> parens (vcat' (map ppe bs)) $+$ indent (vcat' (map ppe es))
  ppe (Letrec bs es)             = parens $ text "letrec" <+> parens (vcat' (map ppe bs)) $+$ indent (vcat' (map ppe es))
  ppe (As e t)                   = parens $ char ':' <+> ppe e <+> ppe t
  ppe (Begin es e)               = parens $ text "begin" $+$ indent (vcat' $ map ppe es) $+$ indent (ppe e)
  ppe (Repeat x a e1 e2 e b (Ann _ t)) =
    parens $ text "repeat" <+> parens (text x <+> ppe e1 <+> ppe e2)
    <+> parens (case t of
                   BlankTy -> text a <+> ppe b
                   _       -> text a <+> (char ':' <+> ppe t) <+> ppe b)
    $+$ ppe e
  ppe (Time e)                   = parens $ text "time" <+> ppe e
  ppe (P p)                      = ppe p

instance Pretty t => Pretty (Type t) where
  ppe BlankTy      = error "blank type should not be prettied"
  ppe Dyn          = text "Dyn"
  ppe CharTy       = text "Char"
  ppe IntTy        = text "Int"
  ppe FloatTy      = text "Float"
  ppe BoolTy       = text "Bool"
  ppe UnitTy       = text "()"
  ppe (FunTy ts t) = parens $ hsep (map ppe ts) <> text " -> " <> ppe t
  ppe (ArrTy ts t) = parens $ hsep (map ppe ts) <> text " -> " <> ppe t
  -- ppe (ArrTy _ _) = error "arrow type should not be prettied"
  ppe (RefTy t)    = parens $ text "Ref" <+> ppe t
  ppe (GRefTy t)   = parens $ text "GRef" <+> ppe t
  ppe (MRefTy t)   = parens $ text "MRef" <+> ppe t
  ppe (VectTy t)   = parens $ text "Vect" <+> ppe t
  ppe (GVectTy t)  = parens $ text "GVect" <+> ppe t
  ppe (MVectTy t)  = parens $ text "MVect" <+> ppe t
  ppe (TupleTy ts) = parens $ text "Tuple" <+> hsep (map ppe ts)
  ppe (VarTy x)    = text x
  ppe (RecTy x t)  = parens $ text "Rec" <+> text x <+> ppe t
