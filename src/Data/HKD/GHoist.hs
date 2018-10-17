{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}

module Data.HKD.GHoist where

import           Data.Functor.Identity
import           GHC.Generics

import           GHC.Exts(Constraint)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Compose((:.)(..))
import           Data.Typeable


gnhoist :: forall a f g constr . 
  (
      GHoist constr (Rep (a f)) (Rep (a g)) f g
    , Generic (a f)
    , Generic (a g)
  )
  => Proxy constr
  -> (forall c . constr c => f c -> g c)
  -> a f
  -> a g 
gnhoist pxy f = to . (ghoist pxy f :: _ (f _) -> _ (g _)) . from


-- | Generic Hoist
class GHoist (constr :: * -> Constraint) i o f g where
  ghoist :: Proxy constr -> (forall b . constr b => f b -> g b) -> i (f p) -> o (g p)

instance (GHoist constr i o f g, GHoist constr i' o' f g) => GHoist constr (i :+: i') (o :+: o') f g where
  ghoist pxy f (L1 l) = L1 $ ghoist pxy f l
  ghoist pxy f (R1 r) = R1 $ ghoist pxy f r  

instance (GHoist constr i o f g, GHoist constr i' o' f g) => GHoist constr (i :*: i') (o :*: o') f g where
  ghoist pxy f (l :*: r) = ghoist pxy f l :*: ghoist pxy f r
  
instance GHoist constr V1 V1 f g where
    ghoist _ _ = undefined

instance {-# OVERLAPPABLE #-} (GHoist constr i o f g) => GHoist constr (M1 _a _b i) (M1 _a' _b' o) f g where
  ghoist pxy f (M1 x) = M1 $ ghoist pxy f x


-- | Nesting structures

-- | Internal node
-- | a g -> a g
instance
  ( Generic (a f)
  , Generic (a g)
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  ) => GHoist constr (K1 c (a f)) (K1 c (a g)) f g where
  ghoist pxy fxn (K1 af) = K1 $ gnhoist pxy fxn af

-- | Nested leaf
-- | f b -> g b
instance
  (constr b)
  => GHoist (constr :: * -> Constraint) (K1 c (f b)) (K1 c (g b)) f g where
  ghoist _ fxn (K1 fb) = K1 $ fxn fb

-- | Nested Internal node
-- | f a f -> g (a g)
instance
  ( Generic (a f)
  , Generic (a g)
  , Functor f
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  , constr (a g)
  ) => GHoist (constr :: * -> Constraint) (K1 c (f (a f))) (K1 c (g (a g))) f g where
  ghoist pxy fxn (K1 faf) = K1 gag
    where
      fag = gnhoist pxy fxn <$> faf
      gag = fxn fag

-- | Nested container of Internal nodes
-- | f (t (a f)) -> g (t (a g))
instance
  ( Generic (a f)
  , Generic (a g)
  , Functor f
  , Functor g
  , Functor t
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  , constr (t (a g))
  ) => GHoist (constr :: * -> Constraint) (K1 c (f (t (a f)))) (K1 c (g (t (a g)))) f g where
  ghoist pxy fxn (K1 ftaf) = K1 gtag
    where
      ftag = fmap (fmap (gnhoist pxy fxn)) ftaf
      gtag = fxn ftag

-- | Container of nested leaves
-- | t (f b) -> t (g b)
instance
  ( Functor f
  , Functor g
  , Functor t
  , constr b
  ) => GHoist (constr :: * -> Constraint) (K1 c (t (f b))) (K1 c (t (g b))) f g where
  ghoist pxy fxn (K1 tfb) = K1 tgb
    where
      tgb = fmap fxn tfb 


-- | Container of internal nodes
-- | t (a f) -> t (a g)
instance
  ( Generic (a f)
  , Generic (a g)
  , Functor t
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  ) => GHoist (constr :: * -> Constraint) (K1 c (t (a f))) (K1 c (t (a g))) f g where
  ghoist pxy fxn (K1 taf) = K1 tag
    where
      tag = fmap (gnhoist pxy fxn) taf

-- | Container of internal nodes
-- | t (f (a f)) -> t (g (a g))
instance
  ( Generic (a f)
  , Generic (a g)
  , Functor f
  , Functor g
  , Functor t
  , constr (a g)
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  ) => GHoist (constr :: * -> Constraint) (K1 c (t (f (a f)))) (K1 c (t (g (a g)))) f g where
  ghoist pxy fxn (K1 tfaf) = K1 tgag
    where
      tfag = fmap (fmap (gnhoist pxy fxn)) tfaf
      tgag = fmap fxn tfag
      





-- | Nested HKD Case
-- instance {-# OVERLAPPABLE #-} 
--   (
--       GHoist (Rep (g (ff :: * -> *))) (Rep (g (gg :: * -> *)))  ff gg
--     , Generic (g ff)
--     , Generic (g gg)    
--   ) => GHoist (K1 a (g ff)) (K1 a (g gg)) ff gg where
--     ghoist (K1 k) = K1 $ gnhoist k
--     {-# INLINE ghoist #-}

-- instance {-# OVERLAPPABLE #-} 
--   (   
--       GHoist (Rep (g (ff :: * -> *))) (Rep (g (gg :: * -> *)))  ff gg      
--     , Generic (g ff)
--     , Generic (g gg)    
--   ) => GHoist (K1 _a [g ff]) (K1 _a [g gg]) ff gg where
--     ghoist (K1 x) = K1 $ gnhoist <$> x
--     {-# INLINE ghoist #-}
  

