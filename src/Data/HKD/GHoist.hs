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


type GHoistable constr a f g =
  (   GHoist constr (Rep (a f)) (Rep (a g)) f g
    , Generic (a f)
    , Generic (a g)
  )


-- | generic hoist which uses both the kind variable
-- f and a string of the field
gnhoist' :: forall a f g constr . GHoistable constr a f g
  => Proxy constr
  -> Maybe String
  -> (forall c . constr c => Maybe String -> f c -> g c)
  -> a f
  -> a g
gnhoist' pxy ms f = to . (ghoist pxy ms f :: _ (f _) -> _ (g _)) . from

-- | specialization of the generic hoist to ignore the
-- name of the field
gnhoist :: forall a f g constr . GHoistable constr a f g
  => Proxy constr
  -> (forall c . constr c => f c -> g c)
  -> a f
  -> a g
gnhoist pxy f = gnhoist' pxy Nothing (const f)



-- | Generic Hoist
class GHoist (constr :: * -> Constraint) i o f g where
  ghoist :: Proxy constr
         -> Maybe String
         -> (forall b . constr b => Maybe String -> f b -> g b)
         -> i (f p)
         -> o (g p)

instance (GHoist constr i o f g, GHoist constr i' o' f g)
  => GHoist constr (i :+: i') (o :+: o') f g where
  ghoist pxy ms f (L1 l) = L1 $ ghoist pxy ms f l
  ghoist pxy ms f (R1 r) = R1 $ ghoist pxy ms f r

instance (GHoist constr i o f g, GHoist constr i' o' f g)
  => GHoist constr (i :*: i') (o :*: o') f g where
  ghoist pxy ms f (l :*: r) = ghoist pxy ms f l :*: ghoist pxy ms f r

instance GHoist constr V1 V1 f g where
    ghoist _ _ _ = undefined

instance {-# OVERLAPPABLE #-} (GHoist constr i o f g)
 => GHoist constr (M1 _a _b i) (M1 _a' _b' o) f g where
  ghoist pxy _ f (M1 x) = M1 $ ghoist pxy Nothing f x

instance {-# OVERLAPPABLE #-}
  (GHoist constr i o f g, Selector _b)
   => GHoist constr (M1 S _b i) (M1 a' _b o) f g where
  ghoist pxy _ f meta@(M1 x) = M1 $ ghoist pxy (Just $ selName meta) f x



-- | Nesting structures

-- | Internal node
-- | a g -> a g
instance
  ( Generic (a f)
  , Generic (a g)
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  ) => GHoist constr (K1 c (a f)) (K1 c (a g)) f g where
  ghoist pxy ms fxn (K1 af) = K1 $ gnhoist' pxy ms fxn af

-- | Nested leaf
-- | f b -> g b
instance {-# OVERLAPPABLE #-}
  (constr b)
  => GHoist (constr :: * -> Constraint) (K1 c (f b)) (K1 c (g b)) f g where
  ghoist _ ms fxn (K1 fb) = K1 $ fxn ms fb

-- | Nested Internal node
-- | f a f -> g (a g)
instance {-# OVERLAPPABLE #-}
  ( Generic (a f)
  , Generic (a g)
  , Functor f
  , GHoist constr (Rep (a f)) (Rep (a g)) f g
  , constr (a g)
  ) => GHoist (constr :: * -> Constraint) (K1 c (f (a f))) (K1 c (g (a g))) f g where
  ghoist pxy ms fxn (K1 faf) = K1 gag
    where
      fag = gnhoist' pxy Nothing fxn <$> faf
      gag = fxn ms fag

-----------------------------------------------
-- | Nested HKD Case (Identity special case)
-- | Internal node
-- | a f -> a Identity
instance
  ( Generic (a f)
  , Generic (a Identity)
  , GHoist constr (Rep (a f)) (Rep (a Identity)) f Identity
  ) => GHoist constr (K1 c (a f)) (K1 c (a Identity)) f Identity where
  ghoist pxy ms fxn (K1 af) = K1 $ gnhoist' pxy ms fxn af

-- | Nested leaf
-- | f b -> b
instance
  (constr b)
  => GHoist (constr :: * -> Constraint) (K1 c (f b)) (K1 c b) f Identity where
  ghoist _ ms fxn (K1 fb) = K1 $ runIdentity $ fxn ms fb

-- | Nested Internal node
-- | f a f -> a Identity
instance
  ( Generic (a f)
  , Generic (a Identity)
  , Functor f
  , GHoist constr (Rep (a f)) (Rep (a Identity)) f Identity
  , constr (a Identity)
  ) => GHoist (constr :: * -> Constraint) (K1 c (f (a f))) (K1 c (a Identity)) f Identity where
  ghoist pxy ms fxn (K1 faf) = K1 gag
    where
      fag = gnhoist' pxy Nothing fxn <$> faf
      gag = runIdentity $ fxn ms fag
