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

module Data.HKD.GTraverse where

import           Data.Functor.Identity
import           GHC.Generics
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Compose((:.)(..), unO)
import           Data.Traversable(sequenceA)
import           Data.Functor.Const
import           Data.HKD.Annotate

class GTraverse i o f where
  gsequence :: i p -> f (o p)
  gsequencebr :: (forall a . f (f a) -> f a) -> i p -> f (o p)


type GSequenceable a f g =
  ( Generic (a (f :. g))
  , Generic (a g)
  , Functor f
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
  )


-- | Generic traverse (sequenceA)
gnsequence :: GSequenceable a f g => a (f :. g) -> f (a g)
gnsequence = fmap to . gsequence . from


gnsequencebr :: GSequenceable a f g
  => (forall b . f (f b) -> f b)
  -> a (f :. g)
  -> f (a g)
gnsequencebr fxn = fmap to . gsequencebr fxn . from


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
  , Generic (a g)
  , Generic (a (f :. g))
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
  ) => GTraverse (K1 c (a (f :. g)))
                 (K1 c (a g))
                 f where

  gsequence (K1 afg) = K1 <$> f_ag
    where
      f_ag = gnsequence afg

  gsequencebr f (K1 afg) = K1 <$> f_ag
    where
      f_ag = gnsequencebr f afg


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
  , Generic (a g)
  , Generic (a (f :. g))
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
  ) => GTraverse (K1 c ((f :. g) (a (f :. g))))
                 (K1 c (g (a g)))
                 f where

  gsequence (K1 (O fg_afg)) = K1 <$> fg_ag
    where
      fgf_ag = fmap (fmap gnsequence) fg_afg
      ffg_ag = fmap commute fgf_ag
      fg_ag = join ffg_ag

  gsequencebr f (K1 (O fg_afg)) = K1 <$> fg_ag
    where
      fgf_ag = fmap (fmap (gnsequencebr f)) fg_afg
      ffg_ag = fmap commute fgf_ag
      fg_ag = f ffg_ag

----------------------------------------------------------------------------


-- | Commute type class
class Commute f g where
  commute :: g (f a) -> f (g a)


newtype Ident' a = Ident' {unIdent' :: Identity a} deriving (Generic, Functor, Show)


instance Applicative (Ident') where
  pure x = Ident' (return x)
  (<*>) (Ident' f) (Ident' x) = Ident' $ f <*> x

instance Monad (Ident') where
  return x = Ident' (return x)
  (>>=) (Ident' (Identity x)) fxn = fxn x

instance Functor f => Commute f Ident' where
  commute (Ident' (Identity fx)) = (Ident' . Identity) <$> fx

instance Functor g => Commute Ident' g where
  commute gfx = (Ident' . Identity) $ (runIdentity . unIdent') <$> gfx

instance Functor f => Commute f Identity where
  commute (Identity fx) = Identity <$> fx

instance Functor g => Commute Identity g where
  commute gfx = Identity $ runIdentity <$> gfx


instance Functor f => Commute f (Annotate a) where
  commute (Annotate note fx) = (Annotate note) <$> fx

instance (Functor f, Functor g1, Commute f g1, Commute f g2) => Commute f (g1 :. g2) where
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
