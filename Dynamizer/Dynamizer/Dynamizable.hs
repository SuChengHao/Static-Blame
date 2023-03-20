{-# LANGUAGE UndecidableInstances #-}

module Dynamizer.Dynamizable where

import           Data.Bifunctor        (bimap)

import           Language.Grift.Common.Syntax
import           Language.Grift.Source.Syntax

class Dynamizable p where
  dynamize :: p -> p

instance Dynamizable (e (Ann a e)) => Dynamizable (Ann a e) where
  dynamize (Ann a e) = Ann a $ dynamize e

instance Dynamizable e => Dynamizable (ProgramF e) where
  dynamize = fmap dynamize

instance Dynamizable e => Dynamizable (ScopeF e) where
  dynamize = fmap dynamize

instance Dynamizable e => Dynamizable (ModuleF e) where
  dynamize = fmap dynamize

instance (Dynamizable t, Dynamizable e) => Dynamizable (BindF t e) where
  dynamize = bimap dynamize dynamize

instance (Dynamizable t, Dynamizable e) => Dynamizable (ExpF t e) where
  dynamize = bimap dynamize dynamize

instance Dynamizable t => Dynamizable (Type t) where
  dynamize t@ArrTy{} = dynamize <$> t
  dynamize _         = Dyn
