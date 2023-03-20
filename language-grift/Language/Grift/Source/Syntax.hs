{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Source.Syntax(
  Name
  , Type(..)
  , ExpF(..)
  , BindF (..)
  , Prim(..)
  , Ann(..)
  , (⊑)) where

import           Algebra.Lattice
import           Data.Bifunctor.TH
import           Language.Grift.Common.Syntax

type Args = [Name]

data BindF t e = Bind Name t e

-- base functor (two-level types trick)
-- structure operator
data ExpF t e =
  DConst Name t e
  | DLam Name Args e t
  | Lam Args e t
  | As e t
  | Repeat Name Name e e e e t
  | Op Operator [e]
  | If e e e
  | Cond [(e, e)]
  | App e [e]
  | Ref e
  | DeRef e
  | Assign e e
  | GRef e
  | GDeRef e
  | GAssign e e
  | MRef e
  | MDeRef e
  | MAssign e e
  | Vect e e -- length value
  | VectRef e e -- vect pos
  | VectSet e e e -- vect pos value
  | GVect e e -- length value
  | GVectRef e e -- vect pos
  | GVectSet e e e -- vect pos value
  | MVect e e
  | MVectRef e e
  | MVectSet e e e
  | Tuple [e]
  | TupleProj e Int
  | Let [BindF t e] [e]
  | Letrec [BindF t e] [e]
  | Begin [e] e
  | Time e
  | P Prim

deriving instance Functor (BindF t)
deriving instance Foldable (BindF t)
deriving instance Traversable (BindF t)

deriving instance Functor (ExpF t)
deriving instance Foldable (ExpF t)
deriving instance Traversable (ExpF t)

$(deriveBifunctor ''BindF)
$(deriveBifoldable ''BindF)
$(deriveBitraversable ''BindF)

$(deriveBifunctor ''ExpF)
$(deriveBifoldable ''ExpF)
$(deriveBitraversable ''ExpF)

data Type t =
  BlankTy
  | Dyn
  | CharTy
  | IntTy
  | FloatTy
  | BoolTy
  | UnitTy
  | FunTy [t] t
  | ArrTy [t] t
  | RefTy t
  | GRefTy t
  | MRefTy t
  | VectTy t
  | GVectTy t
  | MVectTy t
  | TupleTy [t]
  | VarTy Name
  | RecTy Name t
  deriving (Eq,Show,Functor,Foldable,Traversable)

deriving instance (Show a, Show t) => Show (BindF t (Ann a (ExpF t)))
deriving instance (Show a, Show t) => Show (ExpF t (Ann a (ExpF t)))

instance (MeetSemiLattice t, Show t) => MeetSemiLattice (Type t) where
  Dyn /\ t                           = t
  t /\ Dyn                           = t
  CharTy /\ CharTy                   = CharTy
  IntTy /\ IntTy                     = IntTy
  FloatTy /\ FloatTy                 = FloatTy
  BoolTy /\ BoolTy                   = BoolTy
  UnitTy /\ UnitTy                   = UnitTy
  (FunTy ts1 rt1) /\ (FunTy ts2 rt2) =
    FunTy (zipWith (/\) ts1 ts2) $ (/\) rt1 rt2
  (ArrTy ts1 rt1) /\ (ArrTy ts2 rt2) =
    ArrTy (zipWith (/\) ts1 ts2) $ (/\) rt1 rt2
  (RefTy t1) /\ (RefTy t2)           = RefTy $ (/\) t1 t2
  (GRefTy t1) /\ (GRefTy t2)         = GRefTy $ (/\) t1 t2
  (MRefTy t1) /\ (MRefTy t2)         = MRefTy $ (/\) t1 t2
  (VectTy t1) /\ (VectTy t2)         = VectTy $ (/\) t1 t2
  (GVectTy t1) /\ (GVectTy t2)       = GVectTy $ (/\) t1 t2
  (MVectTy t1) /\ (MVectTy t2)       = MVectTy $ (/\) t1 t2
  (TupleTy t1) /\ (TupleTy t2)       = TupleTy $ zipWith (/\) t1 t2
  t1 /\ t2                             =
    error ("/\\: undefined on " ++ show t1 ++ " and " ++ show t2)

instance (JoinSemiLattice t, Show t) => JoinSemiLattice (Type t) where
  Dyn \/ _                           = Dyn
  _ \/ Dyn                           = Dyn
  CharTy \/ CharTy                   = CharTy
  IntTy \/ IntTy                     = IntTy
  FloatTy \/ FloatTy                 = FloatTy
  BoolTy \/ BoolTy                   = BoolTy
  UnitTy \/ UnitTy                   = UnitTy
  (FunTy ts1 rt1) \/ (FunTy ts2 rt2) =
    FunTy (zipWith (\/) ts1 ts2) $ (\/) rt1 rt2
  (ArrTy ts1 rt1) \/ (ArrTy ts2 rt2) =
    ArrTy (zipWith (\/) ts1 ts2) $ (\/) rt1 rt2
  (RefTy t1) \/ (RefTy t2)           = RefTy $ (\/) t1 t2
  (GRefTy t1) \/ (GRefTy t2)         = GRefTy $ (\/) t1 t2
  (MRefTy t1) \/ (MRefTy t2)         = MRefTy $ (\/) t1 t2
  (VectTy t1) \/ (VectTy t2)         = VectTy $ (\/) t1 t2
  (GVectTy t1) \/ (GVectTy t2)       = GVectTy $ (\/) t1 t2
  (MVectTy t1) \/ (MVectTy t2)       = MVectTy $ (\/) t1 t2
  (TupleTy t1) \/ (TupleTy t2)       = TupleTy $ zipWith (\/) t1 t2
  t1 \/ t2                           =
    error ("\\/: undefined on " ++ show t1 ++ " and " ++ show t2)

instance (JoinSemiLattice t, MeetSemiLattice t, Show t) => Lattice (Type t) where

(⊑) :: (Eq t, Show t, JoinSemiLattice t) => Type t -> Type t -> Bool
(⊑) = joinLeq
