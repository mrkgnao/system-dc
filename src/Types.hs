{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric                  #-}
{-# LANGUAGE FlexibleContexts                  #-}
{-# LANGUAGE TypeApplications                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
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
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

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

import           Control.Comonad
import           Control.Lens
import           Control.Monad
import           Control.Monad.Fix
import           Data.Deriving
import           Data.Foldable
import           Data.Function
import           Data.Functor
import           Data.Functor.Classes
import           Data.Maybe
import           Data.Semigroup              (Semigroup)
import           Data.Traversable
import           Data.Type.Equality
import           Data.Unique
import           Data.Void
import GHC.Show

import           Unsafe.Coerce
import GHC.Generics (Generic)

import Pretty

type FamName = Text

type DataConName = Text

type Konst = Text

data Rel = Rel | Irrel deriving (Show, Eq)

type (~>) f g = forall x. f x -> g x
type (|>) f a = forall x. f x -> a

infixl 1 >>-
infixl 1 >>>-
infixr 1 -<<

--------------------------------------------------------------------------------
-- Classes
--
-- Higher-order versions of the standard Prelude classes and others.
--------------------------------------------------------------------------------

class HFunctor (t :: (k -> *) -> k' -> *) where
  hmap :: f ~> g -> t f ~> t g

class HFoldable (t :: (k -> *) -> k' -> *) where
  hfoldMap :: Monoid m => f |> m -> t f |> m

class HFunctor t => HTraversable t where
  htraverse :: forall m f g. Applicative m
            => (forall x.   f x -> m (  g x))
            -> (forall x. t f x -> m (t g x))

class HFunctor t => HMonad t where
  hreturn :: f ~> t f
  (>>-)   :: t f a -> f ~> t g -> t g a

class HBound s where
  (>>>-) :: HMonad t => s t f a -> f ~> t g -> s t g a

class HMonadTrans s where
  hlift :: HMonad t => t f ~> s t f

(-<<) :: HMonad t => f ~> t g -> t f ~> t g
f -<< m = m >>- f

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance HFunctor (Var q b) where
  hmap _ (B b) = B b
  hmap f (F a) = F (f a)

instance HTraversable (Var q b) where
  htraverse _ (B b) = pure (B b)
  htraverse f (F a) = F <$> f a

instance HMonad (Var q b) where
  hreturn   = F
  B b >>- _ = B b
  F a >>- f = f a

instance HFunctor t => HFunctor (Scope q b t) where
  hmap f = Scope . hmap (hmap (hmap f)) . unscope

instance HTraversable t => HTraversable (Scope q b t) where
  htraverse f = fmap Scope . htraverse (htraverse (htraverse f)) . unscope

instance HMonad t => HMonad (Scope q b t) where
  hreturn = Scope . hreturn . F . hreturn
  Scope e >>- f  = Scope (e >>- \case
    B b  -> hreturn (B b)
    F ea -> ea >>- unscope . f)

instance HMonadTrans (Scope q b) where
  hlift = Scope . hreturn . F

instance HBound (Scope q b) where
  Scope m >>>- f = Scope (hmap (hmap (>>- f)) m)

--------------------------------------------------------------------------------
-- Bound types
--------------------------------------------------------------------------------

data Var (q :: k) b f (a :: *) = B (b a) | F (f a)

-- | The tagged higher-order scope transformer.
--
-- 'Scope' @q b t f a@ is a @t f@-expression with bound variables in @b a@ and
-- free variables in @f a@.

newtype Scope q b t f a where
  Scope
    :: forall
         (q :: k)
         (b :: * -> *)
         (t :: (* -> *) -> * -> *)
         (f :: * -> *)
         (a :: *)
     . t (Var q b (t f)) a
    -> Scope q b t f a

unscope :: Scope q b t f a -> t (Var q b (t f)) a
unscope (Scope s) = s

--------------------------------------------------------------------------------
-- Bound operations
--------------------------------------------------------------------------------

-- abstract :: Monad f => (a -> Maybe b) -> f a -> Scope b f a (original)
-- abstract :: Monad t => (f -> Maybe b) -> t f -> Scope b t f (renamed)
abstract
  :: HMonad t => (forall x . f x -> Maybe (b x)) -> (t f ~> Scope q b t f)
abstract f = Scope . hmap
  ( \y -> case f y of
    Just b  -> B b
    Nothing -> F (hreturn y)
  )

instantiate :: HMonad t => b ~> t f -> Scope q b t f ~> t f
instantiate k (Scope e) = e >>- \case
  B b -> k b
  F a -> a

closed :: HTraversable t => t f a -> Maybe (t g a)
closed = htraverse (const Nothing)

(==?) :: TestEquality f => f a -> f b -> Maybe (a :~: b)
(==?) = testEquality

ulam :: forall a . Rel -> V a -> Syn V (Tm a) -> Syn V (Tm a)
ulam rel var body = TmULam rel (abstract (var ==?) body)

uapp :: Rel -> Term f a -> Term f a -> Term f a
uapp = TmApp

fix_term :: Term V a
fix_term = ulam
  Irrel
  (V 0)
  ( ulam
    Rel
    (V 1)
    ( uapp
      Rel
      (SynVar (V 1))
      (uapp Rel (uapp Irrel (SynVar (V 99)) TmBullet) (SynVar (V 1)))
    )
  )

--------------------------------------------------------------------------------

type Term f a = Syn f (Tm a)
type Coer f a = Syn f (Co a)
type Csnt f a = Syn f (Ct a)

newtype Tm a = Tm a deriving (Show, Generic)
newtype Co a = Co a deriving (Show, Generic)
newtype Ct a = Ct a deriving (Show, Generic)

newtype V a = V Int deriving Show

unsafeCastV :: V a -> V b
unsafeCastV (V x) = V x

instance TestEquality V where
  testEquality :: V a -> V b -> Maybe (a :~: b)
  testEquality (V a) (V b)
    | a == b = Just (unsafeCoerce Refl)
    | otherwise = Nothing

type Scope1 a = Scope a V

data Abs = Pi | Lam

type TmScope1 syn f t a = Scope Tm ((:~:) a) syn f (t a)
type CoScope1 syn f t a = Scope Co ((:~:) a) syn f (t a)

-- | Tagged explicit core syntax.
--
-- Since our representation of variable binding is locally nameless,
-- our binding forms will necessarily look different from the 
-- actual paper.
--
-- @\<binding form\>.                      \<body of binding\>@ \(=\)
-- \( {\sf BindingForm}\,\, v. {\sf BindingBody} \)
--
-- @\<binding form\> \<type of variable\>. \<body of binding\>@ \(=\)
-- \( {\sf BindingForm} (v : {\sf TypeOfVariable}). {\sf BindingBody} \)
--
-- For example, \(\Pi^\rho (x:A) \to B\) is represented as 'TmPi' @rho A B@, where @B@ has an extra bound variable in scope, which corresponds to the \(x\) of the original, named syntax.
--
-- In addition, we also abbreviate some constructor arguments for ease of reading:
--
-- @
-- type 'Term' f a = Syn f (Tm a)
-- type 'Coer' f a = Syn f (Co a)
-- type 'Csnt' f a = Syn f (Ct a)
-- @

data Syn (f :: * -> *) (q :: *) where
  -- | Variables.
  SynVar  :: f a -> Syn f a

  -- Term variables.
  -- TmVar  :: f a -> Term f a

  -- | The type of types.
  --
  -- 'TmStar' @=@ \(\star\)
  --
  -- \ 
  TmStar :: Term f a

  -- | Coercions applied to terms.
  --
  -- 'TmConv' @a gamma =@ \(a \triangleright \gamma\)
  --
  -- \ 
  TmConv :: Term f a -> Coer f a -> Term f a

  -- Term binding forms

  -- | Pi-types annotated with relevance.
  --
  -- 'TmPi' @rho A B =@ \( \Pi^\rho A \to B \)
  --
  -- \ 
  TmPi   :: Rel -> Term f a -> TmScope1 Syn f Tm a -> Term f a

  -- | Type-annotated lambda-abstractions, annotated with relevance.
  --
  -- 'TmLam' @rho A b =@ \( \lambda^\rho A. b \)
  --
  -- \ 
  TmLam  :: Rel -> Term f a -> TmScope1 Syn f Tm a -> Term f a

  -- | Implicit lambda-abstractions, annotated with relevance.
  --
  -- 'TmULam' @rho b = @ \( \lambda^\rho. b\)
  --
  -- \ 
  TmULam :: Rel -> TmScope1 Syn f Tm a -> Term f a

  -- | Applications, with relevance
  --
  -- \(a b^\rho\)
  --
  -- \ 
  TmApp :: Rel -> Term f a -> Term f a -> Term f a

  -- Coercion binding forms

  -- | Coercion-level pi-abstraction
  --
  -- @TmCPi phi B@ = \( \forall \phi. B\)
  --
  -- \ 
  TmCPi   :: Csnt f a -> CoScope1 Syn f Tm a -> Term f a

  -- | Coercion-level lambda-abstraction, with type
  --
  -- \( \Lambda \phi. B\)
  --
  -- \ 
  TmCLam  :: Csnt f a -> CoScope1 Syn f Tm a -> Term f a

  -- | Coercion-level lambda-abstraction
  --
  -- \( \Lambda. b\)
  --
  -- \ 
  TmUCLam :: CoScope1 Syn f Tm a -> Term f a

  -- | Coercion application
  --
  -- \(a [\gamma]\)
  --
  -- \ 
  TmCApp  :: Term f a -> Coer f a -> Term f a

  -- Constants

  TmFam :: FamName -> Term f a
  TmKonst :: Konst -> Term f a
  TmDataCon :: DataConName -> Term f a

  TmBullet :: Term f a
  TmCase :: Term f a -> [Term f a] -> Term f a

  -- | \(\bullet\)
  CoTriv :: Coer f a

  -- Coercion variables \(c\).
  -- CoVar :: f a -> Coer f a

  -- | Beta-reduction.
  CoBeta :: Term f a -> Term f a -> Coer f a

  -- | Homogeneous equality.
  CoRefl :: Term f a -> Coer f a

  -- | Homogeneous equality via a coercion.
  CoReflBy :: Coer f a -> Term f a -> Term f a -> Coer f a

  -- | Symmetry
  CoSym :: Coer f a -> Coer f a

  -- Transitivity
  CoTrans :: Coer f a -> Coer f a -> Coer f a

  -- | \(\Pi^\rho \gamma_1 . \gamma_2\)
  CoPiCong  :: Rel -> Coer f a -> TmScope1 Syn f Co a -> Coer f a

  -- | \(\lambda^\rho \gamma_1 . \gamma_2\)
  CoLamCong :: Rel -> Coer f a -> TmScope1 Syn f Co a -> Coer f a

  -- | \(\gamma_1 \gamma_2^\rho\)
  CoAppCong :: Rel -> Coer f a -> Coer f a -> Coer f a

  -- |
  CoPiFst :: Coer f a -> Coer f a

  -- |
  CoCPiFst :: Coer f a -> Coer f a

  -- |
  CoIsoSnd :: Coer f a -> Coer f a

  -- | @CoPiSnd gamma1 gamma2 =@ \(\gamma_1 @ \gamma_2\)
  CoPiSnd :: Coer f a -> Coer f a -> Coer f a

  -- | \(\forall c: \gamma_1 . \gamma_2\)
  CoCPiCong :: Coer f a -> CoScope1 Syn f Co a -> Coer f a

  -- | \(\lambda c: \gamma_1 . \gamma_2 @ \gamma_3\)
  CoCLamCong :: Coer f a -> Coer f a -> CoScope1 Syn f Co a -> Coer f a

  -- | \(\gamma (\gamma_1, \gamma_2)\)
  CoCAppCong :: Coer f a -> Coer f a -> Coer f a -> Coer f a

  -- | \(\gamma @ (\gamma_1 \sim \gamma_2)\)
  CoCPiSnd :: Coer f a -> Coer f a -> Coer f a -> Coer f a

  -- | \(\gamma_1 \triangleright \gamma_2\)
  CoCast :: Coer f a -> Coer f a -> Coer f a

  -- | \(\gamma_1 \sim_A \gamma_2\)
  CoEqCong :: Term f a -> Coer f a -> Coer f a -> Coer f a

  -- | \({\sf conv} \phi_1 \sim_\gamma \phi_2\)
  CoIsoConv :: Csnt f a -> Coer f a -> Csnt f a -> Coer f a

  -- | \({\sf eta} a\)
  CoEta :: Term f a -> Coer f a

  -- | \({\sf left} \gamma \gamma'\)
  CoLeft :: Coer f a -> Coer f a -> Coer f a

  -- | \({\sf right} \gamma \gamma'\)
  CoRight :: Coer f a -> Coer f a -> Coer f a

  CtEqual :: Term f a -> Term f a -> Term f a -> Csnt f a

instance HFunctor Syn where
  hmap = hmapDefault

instance HTraversable Syn where
  htraverse = synTraverse

instance HMonad Syn where
  hreturn = SynVar
  (>>-) = synBind

hmapDefault :: HTraversable t => f ~> g -> t f ~> t g
hmapDefault f = runIdentity . htraverse (Identity . f)

hfoldMapDefault :: (HTraversable h, Monoid m) => f |> m -> h f |> m
hfoldMapDefault f = getConst . htraverse (Const . f)

instance HFoldable Syn where
  hfoldMap = hfoldMapDefault

instance HTraversable t => HFoldable (Scope q b t) where
  hfoldMap = hfoldMapDefault

synTraverse
  :: forall m f g
   . Applicative m
  => (forall x . f x -> m (g x))
  -> (forall x . Syn f x -> m (Syn g x))
synTraverse phi x = case x of
  SynVar v              -> SynVar <$> phi v
  CtEqual t1 t2 t3      -> CtEqual <$> goSyn t2 <*> goSyn t2 <*> goSyn t3
  ---
  TmStar                -> pure TmStar
  TmConv t c            -> TmConv <$> goSyn t <*> goSyn c
  TmPi  r t s           -> TmPi r <$> goSyn t <*> goScope s
  TmLam r t s           -> TmLam r <$> goSyn t <*> goScope s
  TmULam r st           -> TmULam r <$> goScope st
  TmApp r t1 t2         -> TmApp r <$> goSyn t1 <*> goSyn t2
  TmCPi  ct s           -> TmCPi <$> goSyn ct <*> goScope s
  TmCLam ct s           -> TmCLam <$> goSyn ct <*> goScope s
  TmUCLam s             -> TmUCLam <$> goScope s
  TmCApp t c            -> TmCApp <$> goSyn t <*> goSyn c
  TmFam     famName     -> pure (TmFam famName)
  TmKonst   konst       -> pure (TmKonst konst)
  TmDataCon dataConName -> pure (TmDataCon dataConName)
  TmBullet              -> pure TmBullet
  TmCase t ts           -> TmCase <$> goSyn t <*> traverse goSyn ts
  -----
  CoTriv                -> pure CoTriv
  CoBeta t t'           -> CoBeta <$> goSyn t <*> goSyn t'
  CoRefl t              -> CoRefl <$> goSyn t
  CoReflBy c t t'       -> CoReflBy <$> goSyn c <*> goSyn t <*> goSyn t'
  CoSym c1              -> CoSym <$> goSyn c1
  CoTrans c1 c2         -> CoTrans <$> goSyn c1 <*> goSyn c2
  CoPiCong  r c  stc    -> CoPiCong r <$> goSyn c <*> goScope stc
  CoLamCong r c  stc    -> CoLamCong r <$> goSyn c <*> goScope stc
  CoAppCong r c1 c2     -> CoAppCong r <$> goSyn c1 <*> goSyn c2
  CoPiFst  c1           -> CoPiFst <$> goSyn c1
  CoCPiFst c1           -> CoCPiFst <$> goSyn c1
  CoIsoSnd c1           -> CoIsoSnd <$> goSyn c1
  CoPiSnd   c1 c2       -> CoPiSnd <$> goSyn c1 <*> goSyn c2
  CoCPiCong c  s1       -> CoCPiCong <$> goSyn c <*> goScope s1
  CoCLamCong c1 c2 s    -> CoCLamCong <$> goSyn c1 <*> goSyn c2 <*> goScope s
  CoCAppCong c1 c2 c3   -> CoCAppCong <$> goSyn c1 <*> goSyn c2 <*> goSyn c3
  CoCPiSnd   c1 c2 c3   -> CoCPiSnd <$> goSyn c1 <*> goSyn c2 <*> goSyn c3
  CoCast c1 c2          -> CoCast <$> goSyn c1 <*> goSyn c2
  CoEqCong  t  c1 c2    -> CoEqCong <$> goSyn t <*> goSyn c1 <*> goSyn c2
  CoIsoConv ct c  ct'   -> CoIsoConv <$> goSyn ct <*> goSyn c <*> goSyn ct'
  CoEta t               -> CoEta <$> goSyn t
  CoLeft  c1 c2         -> CoLeft <$> goSyn c1 <*> goSyn c2
  CoRight c1 c2         -> CoRight <$> goSyn c1 <*> goSyn c2
 where
  goSyn :: forall x . Syn f x -> m (Syn g x)
  goSyn = htraverse phi
  goScope
    :: forall (s :: ((* -> *) -> * -> *) -> (* -> *) -> * -> *) x
     . (HBound s, HTraversable (s Syn))
    => s Syn f x
    -> m (s Syn g x)
  goScope = htraverse phi

synBind :: forall f g a . Syn f a -> f ~> Syn g -> Syn g a
synBind x phi = case x of
  SynVar v               -> phi v
  CtEqual t1 t2 t3       -> CtEqual (goSyn t1) (goSyn t2) (goSyn t3)
  -----
  TmStar                 -> TmStar
  TmConv tm co           -> TmConv (goSyn tm) (goSyn co)
  TmPi  r tm sc          -> TmPi r (goSyn tm) (goScope sc)
  TmLam r tm sc          -> TmLam r (goSyn tm) (goScope sc)
  TmULam r sctm          -> TmULam r (goScope sctm)
  TmApp r tm1 tm2        -> TmApp r (goSyn tm1) (goSyn tm2)
  TmCPi  ct scco         -> TmCPi (goSyn ct) (goScope scco)
  TmCLam ct scco         -> TmCLam (goSyn ct) (goScope scco)
  TmUCLam sc             -> TmUCLam (goScope sc)
  TmCApp tm co           -> TmCApp (goSyn tm) (goSyn co)
  TmFam     famName      -> TmFam famName
  TmKonst   konst        -> TmKonst konst
  TmDataCon dataConName  -> TmDataCon dataConName
  TmBullet               -> TmBullet
  TmCase tm tms          -> TmCase (goSyn tm) (map goSyn tms)
  -----
  CoTriv                 -> CoTriv
  CoBeta tm tm'          -> CoBeta (goSyn tm) (goSyn tm')
  CoRefl tm              -> CoRefl (goSyn tm)
  CoReflBy co tm tm'     -> CoReflBy (goSyn co) (goSyn tm) (goSyn tm')
  CoSym co1              -> CoSym (goSyn co1)
  CoTrans co1 co2        -> CoTrans (goSyn co1) (goSyn co2)
  CoPiCong  r co  stc    -> CoPiCong r (goSyn co) (goScope stc)
  CoLamCong r co  stc    -> CoLamCong r (goSyn co) (goScope stc)
  CoAppCong r co1 co2    -> CoAppCong r (goSyn co1) (goSyn co2)
  CoPiFst  co1           -> CoPiFst (goSyn co1)
  CoCPiFst co1           -> CoCPiFst (goSyn co1)
  CoIsoSnd co1           -> CoIsoSnd (goSyn co1)
  CoPiSnd   co1 co2      -> CoPiSnd (goSyn co1) (goSyn co2)
  CoCPiCong co  scco1    -> CoCPiCong (goSyn co) (goScope scco1)
  CoCLamCong co1 co2 scc -> CoCLamCong (goSyn co1) (goSyn co2) (goScope scc)
  CoCAppCong co1 co2 co3 -> CoCAppCong (goSyn co1) (goSyn co2) (goSyn co3)
  CoCPiSnd   co1 co2 co3 -> CoCPiSnd (goSyn co1) (goSyn co2) (goSyn co3)
  CoCast co1 co2         -> CoCast (goSyn co1) (goSyn co2)
  CoEqCong  tm co1 co2   -> CoEqCong (goSyn tm) (goSyn co1) (goSyn co2)
  CoIsoConv ct co  ct'   -> CoIsoConv (goSyn ct) (goSyn co) (goSyn ct')
  CoEta tm               -> CoEta (goSyn tm)
  CoLeft  co1 co2        -> CoLeft (goSyn co1) (goSyn co2)
  CoRight co1 co2        -> CoRight (goSyn co1) (goSyn co2)
 where
  goSyn :: Syn f ~> Syn g
  goSyn = (>>- phi)
  goScope :: HBound s => s Syn f a -> s Syn g a
  goScope = (>>>- phi)

singleStep :: Term V a -> Term V a
singleStep (TmApp rel a b) = TmApp rel (singleStep a) b
-- singleStep (TmCApp (TmCLam phi b) g) = instantiate (\Refl -> SynVar (V 2)) b
-- singleStep (TmApp rel (TmLam rel' _A w) a) | rel == rel' = instantiate _ w
singleStep (TmConv (TmConv tm co1) co2) = TmConv tm (CoTrans co1 co2)
singleStep (TmConv tm co) = TmConv (singleStep tm) co
singleStep x = x

lol_term :: Term V a
lol_term = TmConv (TmConv TmStar CoTriv) CoTriv

lol_term' :: Term V a
lol_term' = singleStep lol_term

lol_term'' :: Term V a
lol_term'' = singleStep lol_term'
