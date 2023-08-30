{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Main where

import           Control.Arrow             ((&&&))
import           Control.Monad             (zipWithM)
import           Control.Monad.Trans.Class (lift)
import           Data.List                 (zipWith4)
import           Data.Monoid               (Sum (..))
import           Generic.Random
import           GHC.Generics
import           Numeric.Interval          (Interval, member)
import           System.Random.TF          (seedTFGen)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import           Language.Grift.Common.Syntax
import           Language.Grift.Source.Syntax
import           Language.Grift.Source.Utils

import           Dynamizer.Lattice
import           Dynamizer.Sampling

import           Test.Sampling


deriving instance Generic (f (Ann a f)) => Generic (Ann a f)
deriving instance Generic (Type a)
deriving instance Generic (ProgramF a)
deriving instance Generic (ScopeF a)
deriving instance Generic (ModuleF a)
deriving instance Generic (BindF (Ann a Type) (Ann a (ExpF (Ann a Type))))
deriving instance Generic (ExpF (Ann a Type) (Ann a (ExpF (Ann a Type))))
deriving instance Generic Prim
deriving instance Generic Operator

instance Arbitrary Prim where
  arbitrary = genericArbitraryU

instance Arbitrary Operator where
  arbitrary = genericArbitraryU

instance (Arbitrary a, Generic (f (Ann a f)), Arbitrary (f (Ann a f)), BaseCase (Ann a Type)) => Arbitrary (Ann a f) where
  arbitrary = genericArbitraryU

instance (Arbitrary a) => Arbitrary (ScopeF a) where
  arbitrary = genericArbitraryU

instance (Arbitrary a) => Arbitrary (ModuleF a) where
  arbitrary = genericArbitraryU

instance (Arbitrary a) => Arbitrary (ProgramF a) where
  arbitrary = genericArbitrary'
              ((0  :: W "Script") %
               (10 :: W "Modules") %
               ())

instance (Arbitrary a, BaseCase (Type a)) => Arbitrary (Type a) where
  arbitrary = genericArbitrary'
              ((1  :: W "BlankTy") %
               (1  :: W "Dyn") %
               (10 :: W "CharTy") %
               (10 :: W "IntTy") %
               (10 :: W "FloatTy") %
               (10 :: W "BoolTy") %
               (10 :: W "UnitTy") %
               (10 :: W "FunTy") %
               (0  :: W "ArrTy") % -- causes problems because it can not be Dyn
               (10 :: W "RefTy") %
               (10 :: W "GRefTy") %
               (10 :: W "MRefTy") %
               (10 :: W "VectTy") %
               (10 :: W "GVectTy") %
               (10 :: W "MVectTy") %
               (10 :: W "TupleTy") %
               (10 :: W "VarTy") %
               (10 :: W "RecTy") %
               ())

instance (Arbitrary a
         , BaseCase (Ann a Type)
         , BaseCase (ExpF (Ann a Type) (Ann a (ExpF (Ann a Type))))
         , BaseCase (Ann a (ExpF (Ann a Type)))
         , BaseCase (BindF (Ann a Type) (Ann a (ExpF (Ann a Type))))) => Arbitrary (BindF (Ann a Type) (Ann a (ExpF (Ann a Type)))) where
  arbitrary = genericArbitraryU

instance (Arbitrary a
         , BaseCase (Ann a (ExpF (Ann a Type)))
         , BaseCase (Ann a Type)
         , BaseCase (BindF (Ann a Type) (Ann a (ExpF (Ann a Type))))
         , BaseCase (ExpF (Ann a Type) (Ann a (ExpF (Ann a Type))))) => Arbitrary (ExpF (Ann a Type) (Ann a (ExpF (Ann a Type)))) where
  arbitrary = genericArbitrary' (10 % 10 % 10 % 10 % 10 % 10 % 10 % 10 % 10 % 
                                 10 % 10 % 10 % 10 % 10 % 10 % 10 % 10 % 10 % 
                                 10 % 10 % 10 % 10 % 10 % 10 % 10 % 10 % 10 % 
                                 10 % 10 % 10 % 10 % 10 % 10 % 10 % ())

prop_sampleLessPreciseType :: Ann () Type -> Property
prop_sampleLessPreciseType t =
  forAll (choose (0, static' t)) $ \s -> monadicIO $ do
  maybeType <- lift $ sampleLessPreciseTypeIO t s
  case maybeType of
    Just ty -> assert (static' ty == s)
    Nothing -> assert False

test_sampleOne :: [Ann () Type] -> Int -> IO ([[Ann () Type]], [Interval Int])
test_sampleOne ts nb =
  let ts' = map annotateTypeWithCount ts
      p = getSum $ sum $ map getSnd ts'
      is = genIntervals (fromIntegral nb) $ fromIntegral p/fromIntegral nb
      seeds = map seedTFGen $ zipWith4 (,,,) [0..] [11..] [22..] [3..]
  in do z <- zipWithM (sampleOneIO (p, ts')) is seeds
        return (z, is)

prop_sampleOne :: [Ann () Type] -> Property
prop_sampleOne ts =
  forAll (choose (1, 20)) $ \nb ->
    monadicIO $ do
    (r, is) <- lift $ test_sampleOne ts nb
    let (r', is') = (map fst &&& map snd) $ filter (not . null . fst) $ zip r is
    assert $ and $ zipWith (member . sum . map static') r' is'

prop_funLattice :: Ann () (ExpF (Ann () Type)) -> Property
prop_funLattice p =
  monadicIO $ assert $ length (funLattice p) == 2 ^ getSum (funCount p)

prop_moduleLattice :: ProgramF (Ann () (ExpF (Ann () Type))) -> Property
prop_moduleLattice p@(Modules ms) =
  monadicIO $ assert $ length (moduleLattice p) == 2 ^ length ms
prop_moduleLattice _ = monadicIO $ assert True

main :: IO ()
main = do
  quickCheckWith stdArgs{maxSuccess=200} prop_funLattice
  quickCheckWith stdArgs{maxSuccess=200} prop_sampleLessPreciseType
  quickCheckWith stdArgs{maxSuccess=200} prop_sampleOne
  quickCheckWith stdArgs{maxSize=15, maxSuccess=200} prop_moduleLattice
