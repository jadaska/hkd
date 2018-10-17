{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.HKD.GTraverse where

import           Data.Functor.Identity
import           GHC.Generics
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Compose((:.)(..), unO)
import           Data.Traversable(sequenceA)

class GTraverse i o f where
  gsequence :: i p -> f (o p)



-- | Generic traverse (sequenceA)
gnsequence ::
  (
    Generic (a (f :. g))
  , Generic (a g)
  , Functor f
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f 
  )
  => a (f :. g) -> f (a g)
gnsequence = fmap to . gsequence . from


-- | Generics instances
instance (Applicative f, GTraverse i o f, GTraverse i' o' f)
    => GTraverse (i :*: i') (o :*: o') f where
  gsequence (l :*: r) = (:*:)
                    <$> gsequence l
                    <*> gsequence r
  {-# INLINE gsequence #-}

instance (Functor f, GTraverse i o f, GTraverse i' o' f) 
    => GTraverse (i :+: i') (o :+: o') f where
  gsequence (L1 l) = L1 <$> gsequence l
  gsequence (R1 r) = R1 <$> gsequence r
  {-# INLINE gsequence #-}

instance (Functor f, GTraverse i o f)
    => GTraverse (M1 _a _b i) (M1 _a' _b' o) f where
  gsequence (M1 x) = M1 <$> gsequence x
  {-# INLINE gsequence #-}

instance GTraverse V1 V1 f where
  gsequence = undefined
  {-# INLINE gsequence #-}

instance Applicative f => GTraverse U1 U1 f where
  gsequence U1 = pure U1
  {-# INLINE gsequence #-}



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

-- | Nested leaf
-- | (f :. g) b -> f (g b)
instance Functor f
  => GTraverse (K1 c ((f :. g) b)) (K1 c (g b)) f where
  gsequence (K1 (O fgb)) = K1 <$> fgb
  {-# INLINE gsequence #-}

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

-- | Nested container of internal nodes
-- | (f :. g) (t (a (f :. g))) -> f (g (t (a g)))
instance
  ( Monad f
  , Functor g
  , Commute f g
  , Traversable t
  , Generic (a g)
  , Generic (a (f :. g))
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
  ) => GTraverse (K1 c ((f :. g) (t (a (f :. g)))))
                 (K1 c (g (t (a g))))
                 f where
  
  gsequence (K1 (O fgt_afg)) = K1 <$> fgt_ag
    where
      fgtf_ag = fmap (fmap (fmap gnsequence)) fgt_afg
      fgft_ag = fmap (fmap sequenceA) fgtf_ag
      ffgt_ag = fmap commute fgft_ag
      fgt_ag = join ffgt_ag
      

-- | Container of nested leaves
-- | t ((f :. g) b) -> f (t (g b))
instance
  ( Monad f
  , Functor g
  , Commute f g
  , Traversable t
  ) => GTraverse (K1 c (t((f :. g) b)))
                 (K1 c (t(g b)))
                 f where
  
  gsequence (K1 (t_fg_b)) = K1 <$> ftg_b
    where
      tfg_b = fmap unO t_fg_b
      ftg_b = sequenceA tfg_b
      

-- | Container of internal nodes
-- | t ( (a (f :. g))) -> f (t (a g))
instance
  ( Monad f
  , Functor g
  , Traversable t
  , Generic (a g)
  , Generic (a (f :. g))
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
  ) => GTraverse (K1 c (t ((a (f :. g)))))
                 (K1 c (t((a g))))
                 f where
  
  gsequence (K1 (t_afg)) = K1 <$> ft_ag
    where
      tf_ag   = fmap gnsequence t_afg
      ft_ag   = sequenceA tf_ag


-- | Container of nested internal nodes
-- | t ( (f :. g) (a (f :. g))) -> f (t (g (a g)))
instance
  ( Monad f
  , Functor g
  , Commute f g
  , Traversable t
  , Generic (a g)
  , Generic (a (f :. g))  
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f
  ) => GTraverse (K1 c (t((f :. g) (a (f :. g)))))
                 (K1 c (t (g (a g))))
                 f where
  
  gsequence (K1 (t_fg_afg)) = K1 <$> ftg_ag
    where
      tfg_afg = fmap unO t_fg_afg
      tfgf_ag = fmap (fmap (fmap gnsequence)) tfg_afg
      tffg_ag = fmap (fmap commute) tfgf_ag
      tfg_ag  = fmap join tffg_ag
      ftg_ag  = sequenceA tfg_ag
      

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
    
