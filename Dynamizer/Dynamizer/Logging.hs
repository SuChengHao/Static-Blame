{-# OPTIONS_GHC -fno-warn-orphans #-} 
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE TypeApplications    #-}

module Dynamizer.Logging where

import           Control.Monad.Morph (MFunctor (..))
import           Control.Monad.Prompt (Lift (..))
import           Control.Monad.Logger (MonadLogger, LoggingT (..), NoLoggingT (..), runStderrLoggingT)
import           Data.Random ()
import           Data.Random.RVar (RVarT, runRVarTWith)
import           System.Random.MWC (withSystemRandom)
import           Unsafe.Coerce (unsafeCoerce)

import           Language.Grift.Source.Syntax hiding (Prim)
import           Language.Grift.Common.Pretty
import           Language.Grift.Source.Pretty ()
import           Language.Grift.Source.Utils (cata)


-- alternative design choices:
-- We can not use MonadLogger m => RVarT m because weightedShuffle returns an RVar
-- we can not use MaybeT m (RVar [Ann a Type]) because we will end up with an  RVar (MaybeT m [RVar (Ann a Type)])
runSampling :: forall a m. (MonadLogger (m (RVarT IO)), MFunctor m) => m (RVarT IO) a -> m IO a
runSampling = hoist (withSystemRandom @IO . runRVarTWith id)

runSamplingWithLogging :: LoggingT (RVarT IO) t -> IO t
runSamplingWithLogging = runStderrLoggingT . runSampling

runSamplingWithoutLogging :: NoLoggingT (RVarT IO) t -> IO t
runSamplingWithoutLogging = runNoLoggingT . runSampling

instance MFunctor LoggingT where
    hoist f (LoggingT mx) = LoggingT (f . mx)

instance MFunctor NoLoggingT where
    hoist f = NoLoggingT . f . runNoLoggingT

-- a hack to get around the fact that RVarT constructors are not exported
-- https://stackoverflow.com/questions/41797501/implementing-an-mfunctor-instance-for-rvart/42604118
data Prim a

fromRVarT :: RVarT m a -> (a -> b) -> (forall x. Lift Prim m x -> (x -> b) -> b) -> b
fromRVarT = unsafeCoerce

toRVarT :: (forall b. (a -> b) -> (forall x. Lift Prim m x -> (x -> b) -> b) -> b) -> RVarT m a
toRVarT = unsafeCoerce

instance MFunctor (Lift f) where
  hoist _ (Effect p) = Effect p
  hoist phi (Lift m) = Lift (phi m)

instance MFunctor RVarT where
  hoist phi rv = toRVarT $ \done prm -> fromRVarT rv done (prm . hoist phi)

stringfyType :: forall a. Ann a Type -> String
stringfyType = cata $ \_ ty -> case ty of
  BlankTy -> "Blank"
  VarTy x -> "(Var " ++ x ++ ")"
  _       -> codeGen ty

stringfyTypeList :: forall a. [Ann a Type] -> String
stringfyTypeList = foldMap stringfyType
