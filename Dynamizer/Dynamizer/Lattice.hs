{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module Dynamizer.Lattice where

import           Control.Arrow         ((***), (&&&))
import           Control.Monad         (replicateM)
import           Data.Bifoldable       (Bifoldable, bifoldMap)
import           Data.Bifunctor        (bimap)
import           Data.Bitraversable    (bitraverse)
import qualified Data.DList            as DL
import           Data.Foldable         (fold)
import qualified Data.Map.Strict       as M
import           Data.Maybe            (fromMaybe)
import           Data.Monoid           (Product (..), Sum (..))

import           Language.Grift.Common.Syntax
import           Language.Grift.Source.Syntax
import           Language.Grift.Source.Utils

import           Dynamizer.Dynamizable
import           Dynamizer.Module


embedLocalLattice :: forall a t. Gradual (t (Ann a t))
                  => Ann a (ExpF (Ann a t))
                  -> Ann a (ExpF (DL.DList (Ann a t), Ann a t))
embedLocalLattice (Ann s e) = Ann s $ bimap (\t -> (lattice t, t)) embedLocalLattice e

pick :: forall a t. (Gradual (t (Ann a t)), Ord a)
  => Ann a (ExpF (DL.DList (Ann a t), Ann a t))
  -> M.Map a Int
  -> Ann a (ExpF (Ann a t))
pick (Ann s e) src2indx = Ann s $ bimap pick' (`pick` src2indx) e
  where
    pick' :: (DL.DList (Ann a t), Ann a t) -> Ann a t
    pick' (DL.toList -> ts, t@(Ann s' _)) = maybe t (ts !!) $ M.lookup s' src2indx

replaceTypes :: forall a. Ord a
  => M.Map a (Ann a Type)
  -> Ann a (ExpF (Ann a Type))
  -> Ann a (ExpF (Ann a Type))
replaceTypes src2ty (Ann s e) = Ann s $ bimap replaceTypes' (replaceTypes src2ty) e
  where
    replaceTypes' :: Ann a Type -> Ann a Type
    replaceTypes' t@(Ann s' _) = fromMaybe (dynamize t) $ M.lookup s' src2ty

class Dynamizable p => Gradual p where
  -- Generates the lattice of all possible gradually-typed versions.
  lattice :: p -> DL.DList p
  -- Generates the lattice of all coarce grained gradual typing on the function
  -- level
  funLattice :: p -> DL.DList p
  moduleLattice :: p -> DL.DList p
  -- Counts the number of less percise programs and the number of
  -- all type constructors
  count   :: p -> (Product Integer, Sum Int)
  -- computes the percentage of dynamic code.
  dynamic :: Int -> p -> Double
  dynamic a e =
    if a > 0
    then fromIntegral (a - getSum (static e)) / fromIntegral a
    else 0
  -- counts the number of static type nodes in a program
  static  :: p -> Sum Int
  -- counts the number of functions.
  funCount :: p -> Sum Int

-- TODO: think about defining a generalized notion of Functor, Foldable, and
-- Traversable for Ann and use it here
instance Gradual (e (Ann a e)) => Gradual (Ann a e) where
  lattice    (Ann a e)    = Ann a <$> lattice e
  funLattice (Ann a e)    = Ann a <$> funLattice e
  moduleLattice (Ann a e) = Ann a <$> moduleLattice e
  count      (Ann _ e)    = count e
  static     (Ann _ e)    = static e
  funCount   (Ann _ e)    = funCount e

instance Gradual e => Gradual (ProgramF e) where
  lattice = traverse lattice
  count = foldMap count
  static = foldMap static
  funCount = foldMap funCount
  funLattice = traverse funLattice
  moduleLattice (Modules modules) = Modules <$> traverse moduleLattice modules
  moduleLattice e@Script{} = pure e

instance Gradual e => Gradual (ScopeF e) where
  lattice = traverse lattice
  count = foldMap count
  static = foldMap static
  funCount = foldMap funCount
  funLattice = traverse funLattice
  moduleLattice = pure

instance Gradual e => Gradual (ModuleF e) where
  lattice = traverse lattice
  count = foldMap count
  static = foldMap static
  funCount = foldMap funCount
  funLattice = traverse funLattice
  moduleLattice e = [e, fmap dynamize e]

instance (Gradual t, Gradual e) => Gradual (BindF t e) where
  lattice = traverse lattice
  count = foldMap count
  static = foldMap static
  funCount = foldMap funCount
  funLattice = traverse funLattice
  moduleLattice = pure

instance (Gradual t, Gradual e) => Gradual (ExpF t e) where
  lattice = bitraverse lattice lattice
  count   = bifoldMap count count
  static  = bifoldMap static static

  funLattice e@DLam{} = [e, bimap dynamize dynamize e]
  funLattice e@Lam{}  = [e, bimap dynamize dynamize e]
  funLattice e        = traverse funLattice e

  moduleLattice = pure

  funCount DLam{} = 1
  funCount Lam{}  = 1
  funCount e      = foldMap funCount e

instance Gradual t => Gradual (Type t) where
  lattice Dyn       = pure Dyn
  lattice BlankTy   = pure BlankTy
  lattice t@ArrTy{} = traverse lattice t
  lattice t         = DL.cons Dyn $ traverse lattice t

  count Dyn       = (1, 1)
  count BlankTy   = (1, 1)
  count t@ArrTy{} = foldMap count t
  count t         = ((+1) *** (+1)) $ foldMap count t

  static Dyn       = 0
  static BlankTy   = 0
  static t         = 1 + foldMap static t

  funLattice = pure

  moduleLattice = pure

  funCount = mempty

annotateTypeWithCount :: forall a. Ann a Type -> Ann (a, Sum Int) Type
annotateTypeWithCount = bottomUp $ \a t -> (a, f t)
  where
    f :: Type (Ann (a, Sum Int) Type) -> Sum Int
    f BlankTy   = 0
    f Dyn       = 0
    f t         = 1 + foldMap getSnd t

genLatticeInfo :: forall f a. Bifoldable f
               => ProgramF (Ann a (f (Ann a Type)))
               -> ([Ann (a, Sum Int) Type], Int)
genLatticeInfo = (DL.toList *** getSum) . foldMap localLattice
  where
    localLattice :: Ann a (f (Ann a Type)) -> (DL.DList (Ann (a, Sum Int) Type), Sum Int)
    localLattice (Ann _ e) = bifoldMap ((pure &&& getSnd) . annotateTypeWithCount) localLattice e

coarseLattice :: forall a t. (Modulable t, Gradual t)
              => Int                       -- number of units to gradualize over
              -> ScopeF (Ann a (ExpF t))   -- the input program
              -> [ScopeF (Ann a (ExpF t))] -- the list of partially typed programs
coarseLattice unitCount p = f $ funCount p
  where
    f n | n < 11    = DL.toList $ funLattice p
        | otherwise = coarseLatticeWithAutoDetectedModules unitCount p

coarseLatticeWithAutoDetectedModules :: forall a t. (Modulable t, Gradual t)
                                     => Int                     -- the desired number of modules to
                                                                -- gradualize over. The actual number of
                                                                -- modules will be less than or equal to
                                                                -- that number.
                                     -> ScopeF (Ann a (ExpF t)) -- the input program
                                     -> [ScopeF (Ann a (ExpF t))]
coarseLatticeWithAutoDetectedModules unitCount progrm = 
  map ((`pickModuleConfiguration` progrm) . createConfigurationDescription (computeModules unitCount progrm)) configs
  where
    configs = replicateM unitCount [True, False]

    createConfigurationDescription modulesDescription = 
      M.fromList . fold . zipWith (\moduleDescription config -> map (, config) moduleDescription) modulesDescription
