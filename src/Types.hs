{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Basic types
module Types where

import           Bound.Class
import           Bound.Name
import           Bound.Scope.Simple
import           Bound.Term
import           Bound.Var

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Writer.Strict

import           Data.Text                   (Text)
import qualified Data.Text                   as Text
import qualified Data.Text.IO                as Text
import           Data.Vector                 (Vector)
import qualified Data.Vector                 as Vector

import qualified Hedgehog                    as H
import qualified Hedgehog.Gen                as HG
import qualified Hedgehog.Range              as HR

import           Control.Lens
import           Control.Monad
import           Data.Deriving
import           Data.Foldable
import           Data.Function
import           Data.Functor
import           Data.Functor.Classes
import           Data.Maybe
import           Data.Semigroup              (Semigroup)
import           Data.Traversable
import           Data.Void

-- https://github.com/sweirich/corespec/blob/62dceb43298186b3701c56dca63865f4f0a19f90/src/FcEtt/ett_ott.v

type Scope1 = Scope ()

type FamName = Text

type DataConName = Text

type Konst = Text

data Rel
  = Rel
  | Irrel
  deriving Show

-- | Terms and types
data Tm c t
  = TmStar
  | TmVar t
  | TmConv (Tm c t) (Co t c)
  -- | TmLam Rel (Tm c t) (Scope1 (Tm c) t)
  -- | TmULam Rel (Scope1 (Tm c) t)
  -- | TmApp (Tm c t) Rel (Tm c t)
  -- | TmFam FamName
  -- | TmKonst Konst
  -- | TmPi Rel (Tm c t) (Scope1 (Tm c) t)
  -- | TmCPi (Ct c t) (Scope1 (Tm c) t)
  -- | TmCLam (Ct c t) (Scope1 (Tm c) t)
  -- | TmUCLam (Scope1 (Tm c) t)
  -- | TmBullet
  -- | TmDataCon DataConName
  -- | TmCase (Tm c t) (Brs c t)

data Co t c
  = CoTriv
  | CoVar c
  -- | CoBeta (Tm c a) (Tm c a)
  | CoRefl (Tm c t)
  -- | CoReflBy (Tm c a) (Tm c a) (Co c a)
  | CoSym (Co t c)
  -- | CoTrans (Co c a) (Co c a)
  -- | CoPiCong Rel (Co c a) (Co c a)
  -- | CoLamCong Rel (Co c a) (Co c a)
  -- | CoAppCong (Co c a) Rel (Co c a)
  -- | CoPiFst (Co c a)
  -- | CoCPiFst (Co c a)
  -- | CoIsoSnd (Co c a)
  -- | CoPiSnd (Co c a) (Co c a)
  -- | CoCPiCong (Co c a) (Co c a)
  -- | CoCLamCong (Co c a) (Co c a) (Co c a)
  -- | CoCAppCong (Co c a) (Co c a) (Co c a)
  -- | CoCPiSnd (Co c a) (Co c a) (Co c a)
  -- | CoCast (Co c a) (Co c a)
  -- | CoEqCong (Co c a) (Tm c a) (Co c a)
  -- | CoIsoConv (Ct c a) (Ct c a) (Co c a)
  -- | CoEta (Tm c a)
  -- | CoLeft (Co c a) (Co c a)
  -- | CoRight (Co c a) (Co c a)

-- data Ct c a = CtEq (Tm c a) (Tm c a) (Tm c a)
--   deriving Functor

-- data Brs c a
--   = BrNone
--   | BrOne DataConName (Tm c a) (Brs c a)
--   deriving Functor

-- instance Applicative Tm where
--   pure = return
--   (<*>) = ap

-- instance Monad Tm where
--   return = TmVar
--   tm >>= f = case tm of
--     TmVar a -> f a
--     TmStar -> TmStar
--     TmFam f -> TmFam f
--     TmKonst k -> TmKonst k
--     TmApp x r y -> TmApp (x >>= f) r (y >>= f)
--     TmPi r t s  -> TmPi r (t >>= f) (s >>>= f)
--     TmLam r t s -> TmLam r (t >>= f) (s >>>= f)
--     TmULam r s  -> TmULam r (s >>>= f)
--     TmCPi c s -> TmCPi (c & terms %~ (>>= f)) (s >>>= f)
--     TmCLam c s -> TmCLam (c & terms %~ (>>= f)) (s >>>= f)
--     TmUCLam s -> TmUCLam (s >>>= f)
--     TmBullet -> TmBullet
--     TmDataCon d -> TmDataCon d
--     TmConv t c -> TmConv (t >>= f) (c & terms %~ (>>= f))
--     TmCase _ _ -> undefined

-- class HasTerms t where
--   terms :: Traversal (t a) (t b) (Tm a) (Tm b)

-- instance HasTerms Tm where
--   terms
--     :: forall f a b
--      . Applicative f
--     => (Tm a -> f (Tm b))
--     -> Tm a -> f (Tm b)
--   terms f x = case x of
--     TmApp x r y -> TmApp <$> f x <*> pure r <*> f y
--     TmPi r t s  -> TmPi r <$> f t <*> terms f s
--     TmStar      -> pure TmStar
--     TmVar{}     -> f x

-- instance (Traversable t, HasTerms t) => HasTerms (Scope b t) where
--   terms
--     :: forall f x y
--      . Applicative f
--     => (Tm x -> f (Tm y))
--     -> Scope b t x -> f (Scope b t y)
--   terms f s = Scope <$> traverse (traverse (terms f)) (unscope s)

-- instance HasTerms Co where
--   terms :: Prism (Co a) (Co b) (Tm a) (Tm b)
--   terms = prism CoRefl undefined

-- instance HasTerms Ct where
--   terms
--     :: forall f a b
--      . Applicative f
--     => (Tm a -> f (Tm b))
--     -> Ct a -> f (Ct b)
--   terms f (CtEq a b c) = CtEq <$> f a <*> f b <*> f c

-- instance Show a => Show (Tm c a) where showsPrec = showsPrec1

-- deriveShow1 ''Tm
-- deriveShow1 ''Brs
-- deriveShow1 ''Ct
-- deriveShow1 ''Co
