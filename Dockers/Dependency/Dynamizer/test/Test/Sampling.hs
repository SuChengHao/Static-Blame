{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Test.Sampling where

import           Data.Monoid (Sum (..))
import           Numeric.Interval (Interval)
import           System.Random (RandomGen (..))

import           Language.Grift.Source.Syntax

import           Dynamizer.Lattice
import           Dynamizer.Logging
import           Dynamizer.Sampling

sampleLessPreciseTypeIO :: forall a. Ann a Type
                        -> Int
                        -> IO (Maybe (Ann a Type))
sampleLessPreciseTypeIO t s = runSamplingWithoutLogging $ sampleLessPreciseType (annotateTypeWithCount t) s

sampleOneIO :: forall a generator. RandomGen generator
            => (Int, [Ann (a, Sum Int) Type])
            -> Interval Int
            -> generator
            -> IO [Ann a Type]
sampleOneIO p interval gen = map snd <$> runSamplingWithoutLogging (sampleOne p interval gen)

static' :: Gradual a => a -> Int
static' = getSum . static
