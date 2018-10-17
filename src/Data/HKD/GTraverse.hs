{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.HKD.GTraverse where

import           Data.Functor.Identity
import           GHC.Generics
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Compose((:.)(..), unO)
import           Data.Traversable(sequenceA)

class GTraverse i o f where
  gtraverse :: i p -> f (o p)



-- | Generic traverse (sequenceA)
gntraverse ::
  (
    Generic (a (f :. g))
  , Generic (a g)
  , Functor f
  , GTraverse (Rep (a (f :. g))) (Rep (a g)) f 
  )
  => a (f :. g) -> f (a g)
gntraverse = fmap to . gtraverse . from


-- | Generics instances
instance (Applicative f, GTraverse i o f, GTraverse i' o' f)
    => GTraverse (i :*: i') (o :*: o') f where
  gtraverse (l :*: r) = (:*:)
                    <$> gtraverse l
                    <*> gtraverse r
  {-# INLINE gtraverse #-}

instance (Functor f, GTraverse i o f, GTraverse i' o' f) 
    => GTraverse (i :+: i') (o :+: o') f where
  gtraverse (L1 l) = L1 <$> gtraverse l
  gtraverse (R1 r) = R1 <$> gtraverse r
  {-# INLINE gtraverse #-}

instance (Functor f, GTraverse i o f)
    => GTraverse (M1 _a _b i) (M1 _a' _b' o) f where
  gtraverse (M1 x) = M1 <$> gtraverse x
  {-# INLINE gtraverse #-}

instance GTraverse V1 V1 f where
  gtraverse = undefined
  {-# INLINE gtraverse #-}

instance Applicative f => GTraverse U1 U1 f where
  gtraverse U1 = pure U1
  {-# INLINE gtraverse #-}



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
  
  gtraverse (K1 afg) = K1 <$> f_ag
    where
      f_ag = gntraverse afg

-- | Nested leaf
-- | (f :. g) b -> f (g b)
instance Functor f
  => GTraverse (K1 c ((f :. g) b)) (K1 c (g b)) f where
  gtraverse (K1 (O fgb)) = K1 <$> fgb
  {-# INLINE gtraverse #-}

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
  
  gtraverse (K1 (O fg_afg)) = K1 <$> fg_ag
    where
      fgf_ag = fmap (fmap gntraverse) fg_afg
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
  
  gtraverse (K1 (O fgt_afg)) = K1 <$> fgt_ag
    where
      fgtf_ag = fmap (fmap (fmap gntraverse)) fgt_afg
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
  
  gtraverse (K1 (t_fg_b)) = K1 <$> ftg_b
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
  
  gtraverse (K1 (t_afg)) = K1 <$> ft_ag
    where
      tf_ag   = fmap gntraverse t_afg
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
  
  gtraverse (K1 (t_fg_afg)) = K1 <$> ftg_ag
    where
      tfg_afg = fmap unO t_fg_afg
      tfgf_ag = fmap (fmap (fmap gntraverse)) tfg_afg
      tffg_ag = fmap (fmap commute) tfgf_ag
      tfg_ag  = fmap join tffg_ag
      ftg_ag  = sequenceA tfg_ag
      

class Commute f g where
  commute :: g (f a) -> f (g a)

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
    
