{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE FunctionalDependencies             #-}
{-# LANGUAGE MultiParamTypeClasses             #-}
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
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Basic types
module Types where

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

type CoScope1 b x y = Scope1 b Co x y

-- _Scope
--   :: Iso
--        (Scope t b f a)
--        (Scope t b' f a')
--        (f (Bind t b (f a)))
--        (f (Bind t b' (f a')))
-- _Scope = iso unScope Scope

type Scope1 t = Scope t ()

type FamName = Text

type DataConName = Text

type Konst = Text

data Rel = Rel | Irrel

data Ct x y = CtEq (Tm x y) (Tm x y) (Tm x y)

type ClosedTm = Tm Void Void
type ClosedCo = Co Void Void

newtype CoBind x = CoBind x deriving (Functor, Foldable, Traversable)
newtype TmBind y = TmBind y deriving (Functor, Foldable, Traversable)

data Var t b a = B b | F a deriving (Functor, Foldable, Traversable)

newtype Scope t b f x a = Scope { unScope :: f x (Var t b (f x a)) }
  deriving (Functor, Foldable, Traversable)

-- | Term containing coercion variables of type x and term variables of type y.
data Tm x y where
  -- | Star
  TmStar :: Tm x y

  TmVar  :: TmBind y -> Tm x y

  TmConv :: Tm x y -> Co y x -> Tm x y

  -- Term binding forms

  TmPi   :: Rel -> Tm x y -> Scope1 TmBind Tm x y -> Tm x y
  TmLam  :: Rel -> Tm x y -> Scope1 TmBind Tm x y -> Tm x y
  TmULam :: Rel ->           Scope1 TmBind Tm x y -> Tm x y

  -- Coercion binding forms

  TmCPi   :: Ct x y -> Scope1 CoBind Co y x -> Tm x y
  TmCLam  :: Ct x y -> Scope1 CoBind Co y x -> Tm x y
  TmUCLam ::           Scope1 CoBind Co y x -> Tm x y

  TmApp :: Rel -> Tm x y -> Tm x y -> Tm x y

  -- Constants

  TmFam :: FamName -> Tm x y
  TmKonst :: Konst -> Tm x y
  TmDataCon :: DataConName -> Tm x y

  TmBullet :: Tm x y
  TmCase :: Tm x y -> [Tm x y] -> Tm x y

-- | Coercion containing coercion variables of type x and term variables of type y.
data Co y x where
  -- | Represented as a bullet.
  CoTriv :: Co y x

  -- | Coercion variables.
  CoVar :: CoBind x -> Co y x

  -- | Beta-reduction.
  CoBeta :: Tm x y -> Tm x y -> Co y x

  -- | Homogeneous equality.
  CoVarl :: Tm x y -> Co y x

  -- | Homogeneous equality via a coercion.
  CoVarlBy :: Co y x -> Tm x y -> Tm x y -> Co y x

  -- | Symmetry
  CoSym :: Co y x -> Co y x

  -- Transitivity
  CoTrans :: Co y x -> Co y x -> Co y x

  CoPiCong  :: Rel -> Co y x -> Scope1 TmBind Co y x -> Co y x
  CoLamCong :: Rel -> Co y x -> Scope1 CoBind Co y x -> Co y x
  CoAppCong :: Rel -> Co y x -> Co y x -> Co y x

  CoPiFst :: Co y x -> Co y x
  CoCPiFst :: Co y x -> Co y x
  CoIsoSnd :: Co y x -> Co y x

  -- | @CoPiSnd γ1 γ2 =@ \(\gamma_1 @ \gamma_2\)
  CoPiSnd :: Co y x -> Co y x -> Co y x

  -- | \(\forall c: \gamma_1 . \gamma_2\)
  CoCPiCong :: Co y x -> Co y x -> Co y x

  -- | \(\lambda c: \gamma_1 . \gamma_2 @ \gamma_3\)
  CoCLamCong :: Co y x -> Co y x -> Co y x -> Co y x

  -- | \(g (\gamma_1, \gamma_2)\)
  CoCAppCong :: Co y x -> Co y x -> Co y x -> Co y x

  -- | \(g @ (\gamma_1 ~ \gamma_2)\)
  CoCPiSnd :: Co y x -> Co y x -> Co y x -> Co y x

  -- | \(\gamma_1 \triangleright \gamma_2\)
  CoCast :: Co y x -> Co y x -> Co y x

  -- | \(\gamma_1 \sim_A \gamma_2\)
  CoEqCong :: Tm x y -> Co y x -> Co y x -> Co y x

  -- | \({\sf conv} \phi_1 \sim_\gamma \phi_2\)
  CoIsoConv :: Ct x y -> Co y x -> Ct x y -> Co y x

  -- | \({\sf eta} a\)
  CoEta :: Tm x y -> Co y x

  -- | \({\sf left} \gamma \gamma'\)
  CoLeft :: Co y x -> Co y x -> Co y x

  -- | \({\sf right} \gamma \gamma'\)
  CoRight :: Co y x -> Co y x -> Co y x

bimapCt :: forall x x' y y' . (x -> x') -> (y -> y') -> Ct x y -> Ct x' y'
bimapCt fx fy (CtEq a b c) = CtEq (go a) (go b) (go c)
  where go = bimapTm fx fy

bimapCo :: (y -> y') -> (x -> x') -> Co y x -> Co y' x'
bimapCo fy fx = \case
  CoTriv           -> CoTriv
  CoVar (CoBind x) -> CoVar (CoBind (fx x))

bimapTm :: forall x x' y y' . (x -> x') -> (y -> y') -> Tm x y -> Tm x' y'
bimapTm fx fy =
  let goTm = bimapTm fx fy
      goCo = bimapCo fy fx
      goTmScope :: Bifunctor f => Scope t b f x y -> Scope t b f x' y'
      goTmScope = bimapScope fx fy
      goCoScope :: Bifunctor f => Scope t b f y x -> Scope t b f y' x'
      goCoScope = bimapScope fy fx
  in  \case
        TmStar           -> TmStar
        TmVar (TmBind y) -> TmVar (TmBind (fy y))
        TmConv tm co     -> TmConv (goTm tm) (goCo co)
        TmULam r  sc     -> TmULam r (goTmScope sc)
        TmUCLam sc       -> TmUCLam (goCoScope sc)

instance Bifunctor Tm where bimap = bimapTm
instance Bifunctor Co where bimap = bimapCo
instance Bifunctor Ct where bimap = bimapCt

instance Bifunctor f => Bifunctor (Scope t b f) where bimap = bimapScope

bimapScope
  :: Bifunctor f
  => (x -> x')
  -> (y -> y')
  -> Scope t b f x y
  -> Scope t b f x' y'
bimapScope fx fy = Scope . bimap fx (fmap (bimap fx fy)) . unScope

class (Bifunctor l, Bifunctor r) => Bimonad l r | l -> r, r -> l where
  lreturn :: x -> l x y
  rreturn :: x -> r x y

-- bindCo :: (x -> Co y' x') -> (y -> Tm x' y') -> Co y x -> Co y' x'
-- bindCo cf tf = \case
--   CoVar x -> cf x

-- bindScope
--   :: (x -> x')
--   -> (y -> Tm x' y')
--   -> (x -> Co y' x')
--   -> Scope1 TmBind Tm x y
--   -> Scope1 TmBind (Tm x') y'
-- bindScope xx' yf xf (Scope s) = Scope (bimapTm xx' (fmap (bindTm xx' yf xf)) s)
--  -- Scope (fmap (fmap (fmap (bindTm yf xf))) s)

-- bimapTm :: (x -> x') -> (y -> y') -> Tm x y -> Tm x' y'
-- bimapTm xa yb = \case
--   TmVar y -> TmVar (yb y)

-- bimapCo :: (y -> b) -> (x -> a) -> Co y x -> Co b a
-- bimapCo yb xa = \case
--   CoVar x -> CoVar (xa x)

