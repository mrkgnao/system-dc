{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}

module HPrelude where

import Data.Functor.Const
import Data.Functor.Identity
import Data.Type.Equality

type (~>) f g = forall x. f x -> g x
type (|>) f a = forall x. f x -> a

infixl 1 >>-
infixr 1 -<<

--------------------------------------------------------------------------------
-- Classes
--
-- Higher-order versions of the standard Prelude classes and others.
--------------------------------------------------------------------------------

class HFunctor (t :: (* -> *) -> * -> *) where
  hmap :: f ~> g -> t f ~> t g

class HFoldable (t :: (* -> *) -> * -> *) where
  hfoldMap :: Monoid m => f |> m -> t f |> m

class HFunctor t => HTraversable t where
  htraverse :: forall m f g. Applicative m
            => (forall x.   f x -> m (  g x))
            -> (forall x. t f x -> m (t g x))

class HFunctor t => HMonad t where
  hreturn :: f ~> t f
  (>>-)   :: t f a -> f ~> t g -> t g a

class HMonadTrans s where
  hlift :: HMonad t => t f ~> s t f

(-<<) :: HMonad t => f ~> t g -> t f ~> t g
f -<< m = m >>- f

hmapDefault :: HTraversable t => f ~> g -> t f ~> t g
hmapDefault f = runIdentity . htraverse (Identity . f)

hfoldMapDefault :: (HTraversable h, Monoid m) => f |> m -> h f |> m
hfoldMapDefault f = getConst . htraverse (Const . f)

(==?) :: TestEquality f => f a -> f b -> Maybe (a :~: b)
(==?) = testEquality

