{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
module Data.HKD.Traverse where

import           Data.Functor.Identity
import           Data.HKD.HKDF
import           GHC.Generics
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Compose((:.)(..))
import           Data.Traversable(sequenceA)
import           Data.HKD.Annotate

class GTraverse i o f where
  gsequence :: i p -> f (o p)
  gsequencebr :: (forall a . f (f a) -> f a) -> i p -> f (o p)


-- | Generic traverse (sequenceA)
class HKDSequence f g a where
  hkdsequence :: a (f :. g) -> f (a g)
  default hkdsequence ::
    ( Generic (a (f :. g))
    , Generic (a g)
    , Functor f
    , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
    )
    => a (f :. g) -> f (a g)
  hkdsequence = fmap to . gsequence . from


  hkdsequencebr :: (forall b . f (f b) -> f b) -> a (f :. g) -> f (a g)
  default hkdsequencebr ::
    ( Generic (a (f :. g))
    , Generic (a g)
    , Functor f
    , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
    )
    => (forall b . f (f b) -> f b) -> a (f :. g) -> f (a g)
  hkdsequencebr fxn = fmap to . gsequencebr fxn . from


instance (Applicative f, Traversable t, HKDSequence f g a)
  => HKDSequence f g (HKDF t a) where
  hkdsequence (HKDF tafg) = HKDF <$> sequenceA (hkdsequence <$> tafg :: t (f (a g)))
  hkdsequencebr fxn (HKDF tafg) = HKDF <$> sequenceA (hkdsequencebr fxn <$> tafg :: t (f (a g)))


-- | Generics instances
instance (Applicative f, GTraverse i o f, GTraverse i' o' f)
    => GTraverse (i :*: i') (o :*: o') f where
  gsequence (l :*: r) = (:*:)
                    <$> gsequence l
                    <*> gsequence r

  gsequencebr fxn (l :*: r) = (:*:)
                              <$> gsequencebr fxn l
                              <*> gsequencebr fxn r
  -- {-# INLINE gsequence #-}
  -- {-# INLINE gsequencebr #-}

instance (Functor f, GTraverse i o f, GTraverse i' o' f)
    => GTraverse (i :+: i') (o :+: o') f where
  gsequence (L1 l) = L1 <$> gsequence l
  gsequence (R1 r) = R1 <$> gsequence r

  gsequencebr f (L1 l) = L1 <$> gsequencebr f l
  gsequencebr f (R1 r) = R1 <$> gsequencebr f r
  -- {-# INLINE gsequence #-}
  -- {-# INLINE gsequencebr #-}

instance (Functor f, GTraverse i o f)
    => GTraverse (M1 _a _b i) (M1 _a' _b' o) f where
  gsequence (M1 x) = M1 <$> gsequence x
  gsequencebr f (M1 x) = M1 <$> gsequencebr f x
  -- {-# INLINE gsequence #-}

instance GTraverse V1 V1 f where
  gsequence = undefined
  gsequencebr _ = undefined
  -- {-# INLINE gsequence #-}

instance Applicative f => GTraverse U1 U1 f where
  gsequence U1 = pure U1
  gsequencebr _ U1 = pure U1
  -- {-# INLINE gsequence #-}



-- | Nesting structures

-- | Internal node
-- | a (f :. g) -> f (a g)
instance
  ( Functor f
  , HKDSequence f g a
  ) => GTraverse (K1 c (a (f :. g)))
                 (K1 c (a g))
                 f where

  gsequence (K1 afg) = K1 <$> f_ag
    where
      f_ag = hkdsequence afg

  gsequencebr f (K1 afg) = K1 <$> f_ag
    where
      f_ag = hkdsequencebr f afg


-- | Nested leaf
-- | (f :. g) b -> f (g b)
instance Functor f
  => GTraverse (K1 c ((f :. g) b)) (K1 c (g b)) f where
  gsequence (K1 (O fgb)) = K1 <$> fgb
  gsequencebr _ (K1 (O fgb)) = K1 <$> fgb
  -- {-# INLINE gsequence #-}
  -- {-# INLINE gsequencebr #-}

-- | Nested internal node
-- | (f :. g) (a (f :. g)) -> f (g (a g))
instance
  ( Monad f
  , Functor g
  , Commute f g
  , HKDSequence f g a
  ) => GTraverse (K1 c ((f :. g) (a (f :. g))))
                 (K1 c (g (a g)))
                 f where

  gsequence (K1 (O fg_afg)) = K1 <$> fg_ag
    where
      fgf_ag = fmap (fmap hkdsequence) fg_afg
      ffg_ag = fmap commute fgf_ag
      fg_ag = join ffg_ag

  gsequencebr f (K1 (O fg_afg)) = K1 <$> fg_ag
    where
      fgf_ag = fmap (fmap (hkdsequencebr f)) fg_afg
      ffg_ag = fmap commute fgf_ag
      fg_ag = f ffg_ag


-- | Commute type class
class Commute f g where
  commute :: g (f a) -> f (g a)

instance Functor f => Commute f Identity where
  commute (Identity fx) = Identity <$> fx

instance Functor g => Commute Identity g where
  commute gfx = Identity $ runIdentity <$> gfx


instance Functor f => Commute f (Annotate a) where
  commute (Annotate note fx) = (Annotate note) <$> fx

instance (Functor f, Functor g1, Commute f g1, Commute f g2)
  => Commute f (g1 :. g2) where
  commute (O g1g2fx) = f_g1g2x
    where
      g1fg2x = fmap commute g1g2fx
      fg1g2x = commute g1fg2x
      f_g1g2x = fmap O fg1g2x

-- instance Functor g => Commute (Annotate a) g where
--   commute gfx = (uncurry Annotate) $ unAnnotate <$> gfx



instance Applicative f => Commute f Maybe where
  commute = sequenceA

instance Applicative f => Commute f (Either err) where
  commute = sequenceA

instance Applicative f => Commute f [] where
  commute = sequenceA

instance Functor g => Commute (Reader r) g where
  commute gfx = do
    r <- ask
    return $ (`runReader` r) <$> gfx

instance (Monoid w, Functor f) => Commute f (Writer w) where
  commute wfx = fxn <$> fx
    where
      (fx, w0) = runWriter wfx
      fxn x = tell w0 >> return x
