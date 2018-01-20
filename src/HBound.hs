{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}

module HBound where

import           Control.Lens
import           Data.Text          (Text)
import           Data.Type.Equality
import           GHC.Generics       (Generic)
import           Unsafe.Coerce

import           HPrelude
import           Pretty

--------------------------------------------------------------------------------
-- Bound types
--------------------------------------------------------------------------------

infixl 1 >>>-
class HBound s where
  (>>>-) :: HMonad t => s t f a -> f ~> t g -> s t g a

data Var b f (a :: *) = B (b a) | F (f a)

-- | The higher-order scope transformer.
--
-- 'Scope' @b f a x@ is an @f@-expression with bound variables in @b x@ and
-- free variables in @f a x@.

newtype Scope b f a x where
  Scope
    :: forall
         (b :: * -> *)
         (f :: (* -> *) -> * -> *)
         (a :: * -> *)
         (x :: *)
     . f (Var b (f a)) x
    -> Scope b f a x

unscope :: Scope b f a ~> f (Var b (f a))
unscope (Scope s) = s

--------------------------------------------------------------------------------
-- Bound operations
--------------------------------------------------------------------------------

-- abstract :: Monad f => (a -> Maybe b) -> f a -> Scope b f a (original)
abstract :: HMonad f => (forall x . a x -> Maybe (b x)) -> f a ~> Scope b f a
abstract f = Scope . hmap
  ( \y -> case f y of
    Just b  -> B b
    Nothing -> F (hreturn y)
  )
{-# INLINE abstract #-}

instantiate :: HMonad f => b ~> f a -> Scope b f a ~> f a
instantiate k (Scope e) = e >>- \case
  B b -> k b
  F a -> a
{-# INLINE instantiate #-}

closed :: HTraversable f => f a x -> Maybe (f b x)
closed = htraverse (const Nothing)
{-# INLINE closed #-}

substitute :: (HMonad f, TestEquality a) => a x -> f a x -> f a x -> f a x
substitute a p w = w >>- \b -> case a ==? b of
  Just Refl -> p
  _         -> hreturn b
{-# INLINE substitute #-}

substituteVar :: (HFunctor f, TestEquality a) => a x -> a x -> f a x -> f a x
substituteVar a p = hmap (\b -> case a ==? b of
                                  Just Refl -> p 
                                  _ -> b)
{-# INLINE substituteVar #-}

fromScope :: HMonad f => Scope b f a ~> f (Var b a)
fromScope (Scope s) = s >>- \case
  F e -> hmap F e
  B b -> hreturn (B b)
{-# INLINE fromScope #-}

toScope :: HMonad f => f (Var b a) ~> Scope b f a
toScope e = Scope (hmap (hmap hreturn) e)
{-# INLINE toScope #-}

underScope
  :: HMonad f
  => (f (Var b a) x -> f (Var b a) y)
  -> Scope b f a x
  -> Scope b f a y
underScope f sc = toScope (f (fromScope sc))
{-# INLINE underScope #-}

-- | Lift a natural transformation from @i@ to @j@ into one between scopes.
hoistScope
  :: HFunctor f => (forall a . f a ~> g a) -> Scope b f a ~> Scope b g a
hoistScope t (Scope b) = Scope (t (hmap (hmap t) b))
{-# INLINE hoistScope #-}

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance HFunctor (Var b) where
  hmap _ (B b) = B b
  hmap f (F a) = F (f a)

instance HFoldable (Var b) where
  hfoldMap = hfoldMapDefault

instance HTraversable (Var b) where
  htraverse _ (B b) = pure (B b)
  htraverse f (F a) = F <$> f a

instance HMonad (Var b) where
  hreturn   = F
  B b >>- _ = B b
  F a >>- f = f a

--

instance HFunctor f => HFunctor (Scope b f) where
  hmap f = Scope . hmap (hmap (hmap f)) . unscope

instance HTraversable f => HFoldable (Scope b f) where
  hfoldMap = hfoldMapDefault

instance HTraversable f => HTraversable (Scope b f) where
  htraverse f = fmap Scope . htraverse (htraverse (htraverse f)) . unscope

instance HMonad f => HMonad (Scope b f) where
  hreturn = Scope . hreturn . F . hreturn
  Scope e >>- f  = Scope (e >>- \case
    B b  -> hreturn (B b)
    F ea -> ea >>- unscope . f)

instance HMonadTrans (Scope b) where
  hlift = Scope . hreturn . F

instance HBound (Scope b) where
  Scope m >>>- f = Scope (hmap (hmap (>>- f)) m)

--
