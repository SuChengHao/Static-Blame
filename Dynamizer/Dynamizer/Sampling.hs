{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

module Dynamizer.Sampling where

import           Control.Arrow ((&&&))
import           Control.Monad (foldM, guard, mzero)
import           Data.Functor.Identity (Identity (..))
import           Control.Monad.Logger ( MonadLogger (..), logDebugNS)
import           Control.Monad.Morph (MFunctor (..))
import           Control.Monad.IO.Class (MonadIO)
import           Control.Monad.Trans.Class (MonadTrans, lift)
import           Control.Monad.Trans.Maybe (MaybeT (..))
import qualified Data.DList as DL
import           Data.Function (on)
import           Data.List (nub, sortBy, transpose, zipWith4, zipWith5)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Sum (..))
import           Data.Random.RVar (RVarT)
import           Data.Random.Shuffle.Weighted (weightedShuffle)
import qualified Data.Text as Text (pack)
import           Numeric.Interval (Interval, inf, interval, sup)
import           System.Random (Random, RandomGen (..), randomR, randomRs)
import           System.Random.Shuffle (shuffle')
import           System.Random.TF (seedTFGen)

import           Language.Grift.Common.Syntax
import           Language.Grift.Source.Syntax
import           Language.Grift.Source.Utils

import           Dynamizer.Lattice
import           Dynamizer.Logging


randomList :: (Random a, RandomGen g) => (a,a) -> Int -> g -> [a]
randomList bnds n = take n . randomRs bnds

-- | Sample partially-typed versions uniformally.
sampleUniformally :: forall a. Ord a
                  => ProgramF (Ann a (ExpF (Ann a Type)))   -- ^ The fully-statically typed AST to sample from
                  -> Int                                    -- ^ The number of samples
                  -> [ProgramF (Ann a (ExpF (Ann a Type)))] -- ^ The list of samples
sampleUniformally e ns = map (pick' e . M.fromList . zip tps) $ nub rns
  where
    pick' e' x = fmap ((`pick` x) . embedLocalLattice) e'
    typeinfo = fst $ genLatticeInfo e
    tns = map (getSum . getSnd) typeinfo
    tps = map getFst typeinfo
    rns :: [[Int]]
    rns = transpose $ zipWith5 (\n a b c d -> randomList (0,n) ns $ seedTFGen (a,b,c,d)) tns [0..] [11..] [22..] [33..]

-- | Sample partially-typed versions uniformally. It generates the full lattice before sampling.
sampleUniformally' :: forall a t. Gradual (t (Ann a t))
                   => ProgramF (Ann a (ExpF (Ann a t)))   -- ^ The fully-statically typed AST to sample from
                   -> Int                                 -- ^ The number of samples
                   -> [ProgramF (Ann a (ExpF (Ann a t)))] -- ^ The list of samples
sampleUniformally' e ns =
  let l = DL.toList $ lattice e
  in map (l !!) $ take ns $ nub $ randomRs (0,length l - 1) $ seedTFGen (0, 11, 22, 33)

genIntervals :: Double -> Double -> [Interval Int]
genIntervals intervalsCount intervalWidth =
  if intervalWidth > 1
  then genIntervals1 intervalsCount intervalWidth
  else genIntervals2 intervalsCount intervalWidth
  where g = fromMaybe $ error "genIntervals: internal error"
        genIntervals1 ic iw =
          if ic > 1
          then g (interval (ceiling $ (ic-1)*iw) (floor $ ic*iw)):genIntervals1 (ic-1) iw
          else [g $ interval 0 (floor iw)]
        genIntervals2 ic iw =
          if ic > 1
          then g (interval (ceiling $ (ic-1)*iw) (ceiling $ ic*iw)):genIntervals2 (ic-1) iw
          else [g $ interval 0 (ceiling iw)]

runSampleFromBinsWithLogging :: forall a. (Ord a, Show a)
                             => ProgramF (Ann a (ExpF (Ann a Type)))        -- ^ The fully-statically typed AST to sample from
                             -> Int                                         -- ^ The number of samples in each bin
                             -> Int                                         -- ^ The number of bins
                             -> IO [[ProgramF (Ann a (ExpF (Ann a Type)))]] -- ^ The list of bins, where each is a list of samples
runSampleFromBinsWithLogging ast ns nb = runSamplingWithLogging $ sampleFromBins ast ns nb

runSampleFromBinsWithoutLogging :: forall a. (Ord a, Show a)
                                => ProgramF (Ann a (ExpF (Ann a Type)))        -- ^ The fully-statically typed AST to sample from
                                -> Int                                         -- ^ The number of samples in each bin
                                -> Int                                         -- ^ The number of bins
                                -> IO [[ProgramF (Ann a (ExpF (Ann a Type)))]] -- ^ The list of bins, where each is a list of samples
runSampleFromBinsWithoutLogging ast ns nb = runSamplingWithoutLogging $ sampleFromBins ast ns nb

-- | Sample partially-typed versions from equally-sized bins of type preciseness
sampleFromBins :: forall a m n. (MonadTrans m, MonadLogger (m (RVarT n)), MonadIO n, Ord a, Show a)
               => ProgramF (Ann a (ExpF (Ann a Type)))                 -- ^ The fully-statically typed AST to sample from
               -> Int                                                  -- ^ The number of samples in each bin
               -> Int                                                  -- ^ The number of bins
               -> m (RVarT n) [[ProgramF (Ann a (ExpF (Ann a Type)))]] -- ^ The list of bins, where each is a list of samples
sampleFromBins ast ns nb = do
  let (typeInfo, typesNodesCount) = genLatticeInfo ast
  let intervals = genIntervals (fromIntegral nb) $ fromIntegral $ quot typesNodesCount nb
  let msg = "sampleFrombins: proceeding to sample " ++ show ns ++ " samples from each of the following intervals: " ++ show intervals
  logDebugNS (Text.pack "sampleFrombins") $ Text.pack msg
  mapM (sampleMany ns ast typeInfo typesNodesCount) intervals

sampleMany :: forall a m n. (MonadTrans m, MonadLogger (m (RVarT n)), MonadIO n, Ord a, Show a)
           => Int
           -> ProgramF (Ann a (ExpF (Ann a Type)))
           -> [Ann (a, Sum Int) Type]
           -> Int -- ^ total number of nodes
           -> Interval Int
           -> m (RVarT n) [ProgramF (Ann a (ExpF (Ann a Type)))]
sampleMany samplesCount ast typesInfo typeNodesCount intrval =
  mapM (f . seedTFGen) $ take samplesCount $ zipWith4 (,,,) [0..] [11..] [22..] [33..]
  where
    f (split -> (g1, g2)) = do
      sl <- sampleOne (typeNodesCount, shuffle' typesInfo (length typesInfo) g1) intrval g2
      return $ fmap (replaceTypes (M.fromList sl)) ast

sampleOne :: forall a m n generator. (MonadTrans m, MonadLogger (m (RVarT n)), MonadIO n, RandomGen generator)
          => (Int, [Ann (a, Sum Int) Type])
          -> Interval Int
          -> generator
          ->  m (RVarT n) [(a, Ann a Type)]
sampleOne (potential, ts) (inf &&& sup -> (mn, mx)) generator = do
  logSampleOne $ "using the following shuffled list of types: " ++ stringfyTypeList ts
  logSampleOne $ "target is: " ++ show (mn, mx)
  logSampleOne $ "potential is: " ++ show potential
  fst <$> foldM f ([], (potential, 0, generator)) ts
  where
    logSampleOne :: String -> m (RVarT n) ()
    logSampleOne = logDebugNS (Text.pack "sampleOne") . Text.pack

    f :: ([(a, Ann a Type)], (Int, Int, generator))
      -> Ann (a, Sum Int) Type
      -> m (RVarT n) ([(a, Ann a Type)], (Int, Int, generator))
    f x@(l, (remainingPotential, pickedTypeNodeCount, gen)) staticType@(Ann (a, Sum maxTypeNodeCount) _) = do
      logSampleOne $ "remaining potential: " ++ show remainingPotential
      logSampleOne $ "max local type node count: " ++ show maxTypeNodeCount
      let remainingPotential' = remainingPotential-maxTypeNodeCount
      let lo = max 0 (mn-remainingPotential'-pickedTypeNodeCount)
      let hi = min maxTypeNodeCount (mx-pickedTypeNodeCount)
      let (randomTypeNodeCount, gen') = randomR (lo, hi) gen
      logSampleOne $ "random type node count: " ++ show randomTypeNodeCount ++ " picked from the interval: " ++ show (lo, hi)
      maybeType <- sampleLessPreciseType staticType randomTypeNodeCount
      logSampleOne $ "sampled less precise type: " ++ show (stringfyType <$> maybeType) ++ " from the static type: " ++ stringfyType staticType
      return $ if remainingPotential <= 0 then x else case maybeType of
        Nothing -> (l, (remainingPotential', pickedTypeNodeCount, gen'))
        Just t  -> ((a, t):l, (remainingPotential', pickedTypeNodeCount+randomTypeNodeCount, gen'))

sampleLessPreciseType :: forall a m n. (MonadTrans m, MonadLogger (m (RVarT n)), MonadIO n)
                      => Ann (a, Sum Int) Type
                      -> Int
                      -> m (RVarT n) (Maybe (Ann a Type))
sampleLessPreciseType s = runMaybeT . f s
  where
    logSampleLessPreciseType :: String -> MaybeT (m (RVarT n)) ()
    logSampleLessPreciseType = logDebugNS (Text.pack "sampleLessPreciseType") . Text.pack

    invalidSampling :: forall b. Ann (a, b) Type -> Int -> MaybeT (m (RVarT n)) (Ann a Type)
    invalidSampling t n = do
      logSampleLessPreciseType $ "failed when trying to sample " ++ show n ++ " nodes from " ++ stringfyType t
      mzero

    f :: Ann (a, Sum Int) Type -> Int -> MaybeT (m (RVarT n)) (Ann a Type)
    f t@(Ann (a, _) Dyn)       n | n == 0    = return $ Ann a Dyn
                                 | otherwise = invalidSampling t n
    f t@(Ann (a, _) BlankTy)   n | n == 0    = return $ Ann a BlankTy
                                 | otherwise = invalidSampling t n
    f t@(Ann _ (ArrTy _ _))    0 = invalidSampling t 0
    f t@(Ann (a, Sum n') _)    n | n == n'   = return $ stripSnd t
                                 | n == 0    = return $ Ann a Dyn
    f t@(Ann (a, _) CharTy)    n | n == 1    = return $ Ann a CharTy
                                 | otherwise = invalidSampling t n
    f t@(Ann (a, _) IntTy)     n | n == 1    = return $ Ann a IntTy
                                 | otherwise = invalidSampling t n
    f t@(Ann (a, _) FloatTy)   n | n == 1    = return $ Ann a FloatTy
                                 | otherwise = invalidSampling t n
    f t@(Ann (a, _) BoolTy)    n | n == 1    = return $ Ann a BoolTy
                                 | otherwise = invalidSampling t n
    f t@(Ann (a, _) UnitTy)    n | n == 1    = return $ Ann a UnitTy
                                 | otherwise = invalidSampling t n
    f t@(Ann (a, _) (VarTy x)) n | n == 1    = return $ Ann a $ VarTy x
                                 | otherwise = invalidSampling t n
    f (Ann (a, _) (RefTy t))    n = (Ann a . RefTy) <$> f t (n-1)
    f (Ann (a, _) (GRefTy t))   n = (Ann a . GRefTy) <$> f t (n-1)
    f (Ann (a, _) (MRefTy t))   n = (Ann a . MRefTy) <$> f t (n-1)
    f (Ann (a, _) (VectTy t))   n = (Ann a . VectTy) <$> f t (n-1)
    f (Ann (a, _) (GVectTy t))  n = (Ann a . GVectTy) <$> f t (n-1)
    f (Ann (a, _) (MVectTy t))  n = (Ann a . MVectTy) <$> f t (n-1)
    f (Ann (a, Sum typeConstCount) (FunTy ts t)) n = do
      (rt':ts') <- sampleTypeList (n-1) (typeConstCount-1)  (t:ts)
      return $ Ann a $ FunTy ts' rt'
    f (Ann (a, Sum typeConstCount) (ArrTy ts t)) n = do
      (rt':ts') <- sampleTypeList (n-1) (typeConstCount-1) (t:ts)
      return $ Ann a $ ArrTy ts' rt'
    f (Ann (a, Sum typeConstCount) (TupleTy ts)) n =
      Ann a . TupleTy <$> sampleTypeList (n-1) (typeConstCount-1) ts
    f (Ann (a, _) (RecTy x t))  n = (Ann a . RecTy x) <$> f t (n-1)

    logSampleTypeList :: String -> MaybeT (m (RVarT n)) ()
    logSampleTypeList = logDebugNS (Text.pack "sampleTypeList") . Text.pack

    sampleTypeList :: Int -> Int -> [Ann (a, Sum Int) Type] -> MaybeT (m (RVarT n)) [Ann a Type]
    sampleTypeList target potential ts = do
      logSampleTypeList $ "target is: " ++ show target
      logSampleTypeList $ "potential is: " ++ show potential
      guard $ target <= potential
      -- The indices are needed to reconstruct the result list with the original order
      let typeListWithIndices = tagTypesWithIndices ts
      -- Shuffling the types list weighted with how many nodes in each type
      let typeListWithWeights = createWeightedTypesList typeListWithIndices
      l <- logHelper $ weightedShuffle typeListWithWeights
      reorderTypeList . fst <$> foldM g ([], (potential, 0, seedTFGen (0, 11, 22, 33))) l
        where
          reorderTypeList :: forall x. [(Int, Ann x Type)] -> [Ann x Type]
          reorderTypeList = map snd . sortBy (compare `on` fst)

          tagTypesWithIndices :: forall x. [Ann x Type] -> [(Int, Ann x Type)]
          tagTypesWithIndices = zip [0..]

          createWeightedTypesList = map (\y@(_, Ann (_, Sum x) _) -> (x, y))

          logHelper = lift . lift . hoist (\(Identity x) -> return x)
          
          g :: forall g. RandomGen g
            => ([(Int, Ann a Type)], (Int, Int, g))
            -> (Int, Ann (a, Sum Int) Type)
            -> MaybeT (m (RVarT n)) ([(Int, Ann a Type)], (Int, Int, g))
          g (l', (remainingPotential, pickedTypeNodeCount, gen))
            (indx, staticType@(Ann (_, Sum maxTypeNodeCount) _)) = do
            logSampleTypeList $ "remaining potential: " ++ show remainingPotential
            logSampleTypeList $ "max local type node count: " ++ show maxTypeNodeCount
            let remainingPotential' = remainingPotential-maxTypeNodeCount
            let lo = max 0 (target-remainingPotential'-pickedTypeNodeCount)
            let hi = min maxTypeNodeCount (target-pickedTypeNodeCount)
            let (randomTypeNodeCount, gen') = randomR (lo, hi) gen
            logSampleTypeList $ "random type node count: " ++ show randomTypeNodeCount ++ " picked from the interval: " ++ show (lo, hi)
            maybeType <- f staticType randomTypeNodeCount
            logSampleTypeList $ "sampled less precise type: " ++ stringfyType maybeType ++ " from the static type: " ++ stringfyType staticType
            return ((indx, maybeType):l', (remainingPotential', pickedTypeNodeCount+randomTypeNodeCount, gen'))
