{-# LANGUAGE ExplicitForAll #-}

module Language.Grift.Source.Utils
  ( bottomUp
  , cata
  , para
  , getFst
  , getSnd
  , stripSnd
  ) where

import           Language.Grift.Source.Syntax


cata :: forall a b f. Functor f => (b -> f a -> a) -> Ann b f -> a  
cata f (Ann a e) = f a $ fmap (cata f) e

para :: forall a b f. Functor f => (b -> f (Ann b f, a) -> a) -> Ann b f -> a
para f (Ann a e) = f a $ fmap keepCopy e where
  keepCopy x = (x, para f x)

bottomUp :: forall a b e. Functor e => (a -> e (Ann b e) -> b) -> Ann a e -> Ann b e
bottomUp fn = cata (\a e -> Ann (fn a e) e)

getSnd :: forall a b e. Ann (a, b) e -> b
getSnd (Ann (_, n) _) = n

getFst :: forall a b. Ann (a, b) Type -> a
getFst (Ann (a,_) _) = a

stripSnd :: Ann (a, b) Type -> Ann a Type
stripSnd (Ann (a, _) t) = Ann a $ stripSnd <$> t
