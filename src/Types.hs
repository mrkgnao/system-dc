{-# LANGUAGE DataKinds                  #-}
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

module Types
  (
  -- * Scope
  Var(..),Scope(..),
  -- * \"HPrelude\" classes
  HFunctor(..), HFoldable(..), HTraversable(..),
  HMonad(..),
  -- * Terms
  Syn(..)
  )where

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

import           System.IO.Unsafe
import           Unsafe.Coerce

type FamName = Text

type DataConName = Text

type Konst = Text

data Rel = Rel | Irrel

type (~>) f g = forall x. f x -> g x

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

-- | The tagged scope transformer.
newtype Scope (q :: k) b t f (a :: *) = Scope { unscope :: t (Var q b (t f)) a }

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

-- Lam :: Scope ((:~:) b) Remote f a -> Remote f (b -> a)
-- lam_ :: TestEquality f => f a -> Remote f b -> Remote f (a -> b)
-- lam_ v f = Lam (abstract (v ==?) f)

-- abstract1 :: (Monad t, Eq f) => f -> t f -> Scope Identity t f
-- TmULam :: Rel ->               BindTm Syn f (Tm a) -> Syn f (Tm a)

instantiate :: HMonad t => b ~> t f -> Scope q b t f ~> t f
instantiate k (Scope e) = e >>- \case
  B b -> k b
  F a -> a

closed :: HTraversable t => t f a -> Maybe (t g a)
closed = htraverse (const Nothing)

lam :: forall f a. TestEquality f => f a -> Syn f (Tm a) -> Syn f (Tm a)
lam v f = TmULam Rel (abstract (v ==?) f)

ulam :: forall a. V a -> Syn V (Tm a) -> Syn V (Tm a)
ulam = lam

--------------------------------------------------------------------------------

newtype Tm a = Tm a
newtype Co a = Co a

newtype V a = V Int

unsafeCastV :: V a -> V b
unsafeCastV (V x) = V x

instance TestEquality V where
  testEquality :: V a -> V b -> Maybe (a :~: b)
  testEquality (V a) (V b)
    | a == b = Just (unsafeCoerce Refl)
    | otherwise = Nothing

type Scope1 a = Scope a V
data Ct f a = CtEq (Term f a) (Term f a) (Term f a)
  -- deriving (Show)

type Term f a = Syn f (Tm a)
type Coer f a = Syn f (Co a)

data Abs = Pi | Lam

type BindTm syn f t a = Scope Tm ((:~:) a) syn f (t a)
type BindCo syn f t a = Scope Co ((:~:) a) syn f (t a)

instance Show1 ((:~:) a) where
  liftShowsPrec _ _ _ Refl = showString "Refl"

instance Show2 (:~:) where
  liftShowsPrec2 _ _ _ _ _ Refl = showString "Refl"

-- syn :: Term Identity String
-- syn = SynVar (Identity (Tm "asdf"))

-- slam :: Term Identity String
-- slam = TmULam Irrel (abstract (const Nothing) syn)

-- | Tagged explicit core syntax.
data Syn (f :: * -> *) (q :: *) where
  -- | Variables.
  SynVar  :: f a -> Syn f a

  -- Term variables.
  -- TmVar  :: f a -> Syn f (Tm a)

  -- | The type of types.
  --
  -- 'TmStar' @=@ \(\star\)
  TmStar :: Syn f (Tm a)

  -- | Coercions applied to terms.
  --
  -- 'TmConv' @a gamma =@ \(a \triangleright \gamma\)
  TmConv :: Syn f (Tm a) -> Syn f (Co a) -> Syn f (Tm a)

  -- Term binding forms

  -- | Pi-types annotated with relevance.
  --
  -- 'TmPi' @rho A B =@ \( \Pi^\rho A \to B \)
  TmPi   :: Rel -> Syn f (Tm a) -> BindTm Syn f Tm a -> Syn f (Tm a)

  -- | Type-annotated lambda-abstractions, annotated with relevance.
  --
  -- 'TmLam' @rho A b =@ \( \lambda^\rho A. b \)
  TmLam  :: Rel -> Syn f (Tm a) -> BindTm Syn f Tm a -> Syn f (Tm a)

  -- | Implicit lambda-abstractions, annotated with relevance.
  --
  -- 'TmULam' @rho b = @ \( \lambda^\rho. b\)
  TmULam :: Rel ->               BindTm Syn f Tm a -> Syn f (Tm a)

  -- | Applications, with relevance
  --
  -- \(a b^\rho\)
  TmApp :: Rel -> Syn f (Tm a) -> Syn f (Tm a) -> Syn f (Tm a)

  -- Coercion binding forms

  -- | Coercion-level pi-abstraction
  --
  -- @TmCPi phi B@ = \( \forall \phi. B\)
  TmCPi   :: Ct f a -> BindCo Syn f Tm a -> Syn f (Tm a)

  -- | Coercion-level lambda-abstraction, with type
  --
  -- \( \Lambda \phi. B\)
  TmCLam  :: Ct f a -> BindCo Syn f Tm a -> Syn f (Tm a)

  -- | Coercion-level lambda-abstraction
  --
  -- \( \Lambda. b\)
  TmUCLam ::           BindCo Syn f Tm a -> Syn f (Tm a)

  -- | \(a [\gamma]\)
  --
  -- Coercion application
  TmCApp  :: Syn f (Tm a) -> Syn f (Co a) -> Syn f (Tm a)

  -- Constants

  TmFam :: FamName -> Syn f (Tm a)
  TmKonst :: Konst -> Syn f (Tm a)
  TmDataCon :: DataConName -> Syn f (Tm a)

  TmBullet :: Syn f (Tm a)
  TmCase :: Syn f (Tm a) -> [Syn f (Tm a)] -> Syn f (Tm a)

  -- | \(\bullet\)
  CoTriv :: Syn f (Co a)

  -- Coercion variables \(c\).
  -- CoVar :: f a -> Syn f (Co a)

  -- | Beta-reduction.
  CoBeta :: Syn f (Tm a) -> Syn f (Tm a) -> Syn f (Co a)

  -- | Homogeneous equality.
  CoRefl :: Syn f (Tm a) -> Syn f (Co a)

  -- | Homogeneous equality via a coercion.
  CoReflBy :: Syn f (Co a) -> Syn f (Tm a) -> Syn f (Tm a) -> Syn f (Co a)

  -- | Symmetry
  CoSym :: Syn f (Co a) -> Syn f (Co a)

  -- Transitivity
  CoTrans :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \(\Pi^\rho \gamma_1 . \gamma_2\)
  CoPiCong  :: Rel -> Syn f (Co a) -> BindTm Syn f Co a -> Syn f (Co a)

  -- | \(\lambda^\rho \gamma_1 . \gamma_2\)
  CoLamCong :: Rel -> Syn f (Co a) -> BindTm Syn f Co a -> Syn f (Co a)

  -- | \(\gamma_1 \gamma_2^\rho\)
  CoAppCong :: Rel -> Syn f (Co a) ->           Syn f (Co a) -> Syn f (Co a)

  -- |
  CoPiFst :: Syn f (Co a) -> Syn f (Co a)

  -- |
  CoCPiFst :: Syn f (Co a) -> Syn f (Co a)

  -- |
  CoIsoSnd :: Syn f (Co a) -> Syn f (Co a)

  -- | @CoPiSnd γ1 γ2 =@ \(\gamma_1 @ \gamma_2\)
  CoPiSnd :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \(\forall c: \gamma_1 . \gamma_2\)
  CoCPiCong :: Syn f (Co a) -> BindCo Syn f Co a -> Syn f (Co a)

  -- | \(\lambda c: \gamma_1 . \gamma_2 @ \gamma_3\)
  CoCLamCong :: Syn f (Co a) -> Syn f (Co a) -> BindCo Syn f Co a -> Syn f (Co a)

  -- | \(\gamma (\gamma_1, \gamma_2)\)
  CoCAppCong :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \(\gamma @ (\gamma_1 \sim \gamma_2)\)
  CoCPiSnd :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \(\gamma_1 \triangleright \gamma_2\)
  CoCast :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \(\gamma_1 \sim_A \gamma_2\)
  CoEqCong :: Syn f (Tm a) -> Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \({\sf conv} \phi_1 \sim_\gamma \phi_2\)
  CoIsoConv :: Ct f a -> Syn f (Co a) -> Ct f a -> Syn f (Co a)

  -- | \({\sf eta} a\)
  CoEta :: Syn f (Tm a) -> Syn f (Co a)

  -- | \({\sf left} \gamma \gamma'\)
  CoLeft :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

  -- | \({\sf right} \gamma \gamma'\)
  CoRight :: Syn f (Co a) -> Syn f (Co a) -> Syn f (Co a)

instance HFunctor Syn where
  hmap = hmapDefault

instance HTraversable Syn where
  htraverse = synTraverse

instance HFunctor Ct where
  hmap f (CtEq a b c) = CtEq (hmap f a) (hmap f b) (hmap f c)

instance HMonad Syn where
  hreturn = SynVar
  (>>-) = synBind

hmapDefault :: HTraversable t => f ~> g -> t f ~> t g
hmapDefault f = runIdentity . htraverse (Identity . f)

hfoldMapDefault :: (HTraversable h, Monoid m) => f |> m -> h f |> m
hfoldMapDefault f = getConst . htraverse (Const . f)

type (|>) f a = forall x. f x -> a

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
  ---
  TmStar                -> pure TmStar
  TmConv t c            -> TmConv <$> goSyn t <*> goSyn c
  TmPi  r t s           -> TmPi r <$> goSyn t <*> goScope s
  TmLam r t s           -> TmLam r <$> goSyn t <*> goScope s
  TmULam r st           -> TmULam r <$> goScope st
  TmApp r t1 t2         -> TmApp r <$> goSyn t1 <*> goSyn t2
  TmCPi  ct s           -> TmCPi <$> goCt ct <*> goScope s
  TmCLam ct s           -> TmCLam <$> goCt ct <*> goScope s
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
  CoIsoConv ct c  ct'   -> CoIsoConv <$> goCt ct <*> goSyn c <*> goCt ct'
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
  goCt :: forall x . Ct f x -> m (Ct g x)
  goCt (CtEq a b c) = CtEq <$> goSyn a <*> goSyn b <*> goSyn c

synBind :: forall f g a . Syn f a -> f ~> Syn g -> Syn g a
synBind x phi = case x of
  SynVar v               -> phi v
  -----
  TmStar                 -> TmStar
  TmConv tm co           -> TmConv (goSyn tm) (goSyn co)
  TmPi  r tm sc          -> TmPi r (goSyn tm) (goScope sc)
  TmLam r tm sc          -> TmLam r (goSyn tm) (goScope sc)
  TmULam r sctm          -> TmULam r (goScope sctm)
  TmApp r tm1 tm2        -> TmApp r (goSyn tm1) (goSyn tm2)
  TmCPi  ct scco         -> TmCPi (goCt ct) (goScope scco)
  TmCLam ct scco         -> TmCLam (goCt ct) (goScope scco)
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
  CoIsoConv ct co  ct'   -> CoIsoConv (goCt ct) (goSyn co) (goCt ct')
  CoEta tm               -> CoEta (goSyn tm)
  CoLeft  co1 co2        -> CoLeft (goSyn co1) (goSyn co2)
  CoRight co1 co2        -> CoRight (goSyn co1) (goSyn co2)
 where
  goSyn :: Syn f ~> Syn g
  goSyn = (>>- phi)
  goScope :: HBound s => s Syn f a -> s Syn g a
  goScope = (>>>- phi)
  goCt :: Ct f ~> Ct g
  goCt (CtEq a b c) = CtEq (goSyn a) (goSyn b) (goSyn c)

-- Type-level list stuff

data Ix :: [*] -> * -> * where
  Z :: Ix (a ': as) a
  S :: Ix as b -> Ix (a ': as) b

data HVec :: (* -> *) -> [*] -> * where
  HNil :: HVec f '[]
  HCons :: f b -> HVec f bs -> HVec f (b ': bs)

infixr 5 ++

-- | Concat lists of types.
type family (++) (as :: [*]) (bs :: [*]) :: [*] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

hconcat :: HVec f as -> HVec f bs -> HVec f (as ++ bs)
hconcat HNil         bs = bs
hconcat (HCons a as) bs = HCons a (hconcat as bs)

hsingleton :: f a -> HVec f '[a]
hsingleton x = HCons x HNil

instance HFunctor HVec where
  hmap _ HNil         = HNil
  hmap f (HCons x xs) = HCons (f x) (hmap f xs)

instance HTraversable HVec where
  htraverse _ HNil         = pure HNil
  htraverse f (HCons x xs) = HCons <$> f x <*> htraverse f xs

(==?) :: TestEquality f => f a -> f b -> Maybe (a :~: b)
(==?) = testEquality

(!) :: HVec f v -> Ix v a -> f a
(!) (HCons b _ ) Z     = b
(!) (HCons _ bs) (S n) = bs ! n


-- deriving instance (Show1 f, Show a) => Show (Syn f a)
-- newtype Scope b t f a = Scope { unscope :: t (Var b (t f)) a }
-- data Remote :: (* -> *) -> * -> * where
--   Var :: f a -> Remote f a
--   Lit :: a -> Remote f a
--   Lam :: Scope ((:~:) b) Remote f a -> Remote f (b -> a)
--   Let :: HVec (Scope (Ix bs) Remote f) bs -> Scope (Ix bs) Remote f a -> Remote f a
--   Ap  :: Remote f (a -> b) -> Remote f a -> Remote f b

-- lit :: a -> Remote f a
-- lit = Lit

-- instance HFunctor Remote where
--   hmap f (Var a)    = Var (f a)
--   hmap _ (Lit t)    = Lit t
--   hmap f (Lam b)    = Lam (hmap f b)
--   hmap f (Let bs b) = Let (hmap (hmap f) bs) (hmap f b)
--   hmap f (Ap x y)   = Ap (hmap f x) (hmap f y)

-- instance HTraversable Remote where
--   htraverse f (Var a)    = Var <$> f a
--   htraverse _ (Lit t)    = pure $ Lit t
--   htraverse f (Lam b)    = Lam <$> htraverse f b
--   htraverse f (Let bs b) = Let <$> htraverse (htraverse f) bs <*> htraverse f b
--   htraverse f (Ap x y)   = Ap <$> htraverse f x <*> htraverse f y

-- instance HMonad Remote where
--   hreturn        = Var
--   Var a    >>- f = f a
--   Lit t    >>- _ = Lit t
--   Lam b    >>- f = Lam (b >>>- f)
--   Let bs b >>- f = Let (hmap (>>>- f) bs) (b >>>- f)
--   Ap x y   >>- f = Ap (x >>- f) (y >>- f)

-- eval :: Remote Identity a -> a
-- eval (Var w) = extract w
-- eval (Lit i) = i
-- eval (Lam b) = \a -> eval (instantiate (\Refl -> Var (Identity a)) b)
-- eval (Let bs b) = eval (instantiate (vs !) b) where vs = hmap (instantiate (vs !)) bs
-- eval (Ap x y) = eval x (eval y)

-- newtype V (a :: *) = V Unique

-- instance TestEquality V where
--   V a `testEquality` V b
--     | a == b    = Just (unsafeCoerce Refl)
--     | otherwise = Nothing

-- lam :: (Remote V a -> Remote V b) -> Remote V (a -> b)
-- lam f = unsafePerformIO $ do
--   x <- fmap V newUnique
--   return $ Lam $ abstract (x ==?) $ f $ Var x

-- data Binding a = V a := Remote V a

-- rhs :: Binding a -> Remote V a
-- rhs (_ := a) = a

-- data Bindings = forall bs. Bindings (HVec Binding bs)

-- elemIndex :: HVec Binding bs -> V a -> Maybe (Ix bs a)
-- elemIndex HNil              _ = Nothing
-- elemIndex ((x := r) `HCons` xs) y = case x ==? y of
--   Just Refl -> Just Z
--   Nothing   -> S <$> elemIndex xs y

-- instance Monoid Bindings where
--   mempty = Bindings HNil
--   Bindings xs `mappend` Bindings ys = Bindings (hconcat xs ys)

-- -- Allow the use of DoRec to define let statements

-- newtype Def a = Def { runDef :: IO (a, Bindings) }

-- instance Functor Def where
--   fmap f (Def m) = Def $ do
--     (a,w) <- m
--     return (f a, w)

-- instance Applicative Def where
--   pure = return
--   (<*>) = ap

-- instance Monad Def where
--   return a = Def $ return (a, mempty)
--   Def m >>= f = Def $ do
--     (a, xs) <- m
--     (b, ys) <- runDef (f a)
--     return (b, xs <> ys)

-- instance MonadFix Def where
--   mfix m = Def $ mfix $ \ ~(a, _) -> runDef (m a)

-- def :: Remote V a -> Def (Remote V a)
-- def v@Var{} = Def $ return (v, mempty) -- this thing already has a name
-- def r = Def $ do
--   v <- fmap V newUnique
--   return (Var v, Bindings (hsingleton (v := r)))

-- let_ :: Def (Remote V a) -> Remote V a
-- let_ (Def m) = unsafePerformIO $ do
--     (r, Bindings bs) <- m
--     return $ Let (hmap (abstract (elemIndex bs) . rhs) bs)
--                  (abstract (elemIndex bs) r)
--
--synMap :: forall f g . f ~> g -> Syn f ~> Syn g
--synMap phi x = case x of
--  SynVar v              -> SynVar (phi v)
--  -----
--  TmStar                -> TmStar
--  TmConv t c            -> TmConv (goSyn t) (goSyn c)
--  TmPi  r t s           -> TmPi r (goSyn t) (goScope s)
--  TmLam r t s           -> TmLam r (goSyn t) (goScope s)
--  TmULam r st           -> TmULam r (goScope st)
--  TmApp r t1 t2         -> TmApp r (goSyn t1) (goSyn t2)
--  TmCPi  ct s           -> TmCPi (goCt ct) (goScope s)
--  TmCLam ct s           -> TmCLam (goCt ct) (goScope s)
--  TmUCLam s             -> TmUCLam (goScope s)
--  TmCApp t c            -> TmCApp (goSyn t) (goSyn c)
--  TmFam     famName     -> TmFam famName
--  TmKonst   konst       -> TmKonst konst
--  TmDataCon dataConName -> TmDataCon dataConName
--  TmBullet              -> TmBullet
--  TmCase t ts           -> TmCase (goSyn t) (map goSyn ts)
--  -----
--  CoTriv                -> CoTriv
--  CoBeta t t'           -> CoBeta (goSyn t) (goSyn t')
--  CoRefl t              -> CoRefl (goSyn t)
--  CoReflBy c t t'       -> CoReflBy (goSyn c) (goSyn t) (goSyn t')
--  CoSym c1              -> CoSym (goSyn c1)
--  CoTrans c1 c2         -> CoTrans (goSyn c1) (goSyn c2)
--  CoPiCong  r c  stc    -> CoPiCong r (goSyn c) (goScope stc)
--  CoLamCong r c  stc    -> CoLamCong r (goSyn c) (goScope stc)
--  CoAppCong r c1 c2     -> CoAppCong r (goSyn c1) (goSyn c2)
--  CoPiFst  c1           -> CoPiFst (goSyn c1)
--  CoCPiFst c1           -> CoCPiFst (goSyn c1)
--  CoIsoSnd c1           -> CoIsoSnd (goSyn c1)
--  CoPiSnd   c1 c2       -> CoPiSnd (goSyn c1) (goSyn c2)
--  CoCPiCong c  s1       -> CoCPiCong (goSyn c) (goScope s1)
--  CoCLamCong c1 c2 s    -> CoCLamCong (goSyn c1) (goSyn c2) (goScope s)
--  CoCAppCong c1 c2 c3   -> CoCAppCong (goSyn c1) (goSyn c2) (goSyn c3)
--  CoCPiSnd   c1 c2 c3   -> CoCPiSnd (goSyn c1) (goSyn c2) (goSyn c3)
--  CoCast c1 c2          -> CoCast (goSyn c1) (goSyn c2)
--  CoEqCong  t  c1 c2    -> CoEqCong (goSyn t) (goSyn c1) (goSyn c2)
--  CoIsoConv ct c  ct'   -> CoIsoConv (goCt ct) (goSyn c) (goCt ct')
--  CoEta t               -> CoEta (goSyn t)
--  CoLeft  c1 c2         -> CoLeft (goSyn c1) (goSyn c2)
--  CoRight c1 c2         -> CoRight (goSyn c1) (goSyn c2)
-- where
--  goSyn :: Syn f ~> Syn g
--  goSyn = hmap phi
--  goScope
--    :: forall (s :: ((* -> *) -> * -> *) -> (* -> *) -> * -> *)
--     . (HBound s, HFunctor (s Syn))
--    => s Syn f ~> s Syn g
--  goScope = hmap phi
--  goCt :: Ct f ~> Ct g
--  goCt (CtEq a b c) = CtEq (goSyn a) (goSyn b) (goSyn c)

