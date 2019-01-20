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

module Data.HKD.GZip where

import           Data.Functor.Identity
import           GHC.Generics

import           GHC.Exts(Constraint)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Compose((:.)(..))
import           Data.Typeable


type GZippable constr a f g =
  (   GZip constr (Rep (a f)) (Rep (a g)) f g
    , Generic (a f)
    , Generic (a g)
  )

gnzip :: forall a f g constr . GZippable constr a f g
  => Proxy constr
  -> (forall c . constr c => f c -> Maybe (f c) -> g c)
  -> a f
  -> Maybe (a f)
  -> a g
gnzip pxy f x mx = to (gzip pxy f (from x :: _ (f _)) (from <$> mx) :: _ (g _))


-- | Generic Zip
class GZip (constr :: * -> Constraint) i o f g where
  gzip :: Proxy constr
      -> (forall b . constr b => f b -> Maybe (f b) -> g b)
      -> i (f p)
      -> Maybe (i (f p))
      -> o (g p)


instance (GZip constr i o f g, GZip constr i' o' f g)
  => GZip constr (i :+: i') (o :+: o') f g where
  gzip pxy f (L1 l) x = L1 $
    case x of
      (Just (L1 l2)) -> gzip pxy f l (Just l2)
      _              -> gzip pxy f l Nothing
  gzip pxy f (R1 r) x = R1 $
    case x of
      (Just (R1 r2)) -> gzip pxy f r (Just r2)
      _              -> gzip pxy f r Nothing


instance (GZip constr i o f g, GZip constr i' o' f g)
  => GZip constr (i :*: i') (o :*: o') f g where
  gzip pxy f (l :*: r) (Just (l' :*: r')) = gzip pxy f l (Just l') :*: gzip pxy f r (Just r')
  gzip pxy f (l :*: r) Nothing = gzip pxy f l Nothing :*: gzip pxy f r Nothing

instance GZip constr V1 V1 f g where
    gzip _ _ _ _ = undefined

instance {-# OVERLAPPABLE #-} (GZip constr i o f g)
  => GZip constr (M1 _a _b i) (M1 _a' _b' o) f g where
  gzip pxy f (M1 x) (Just (M1 x2)) = M1 $ gzip pxy f x (Just x2)
  gzip pxy f (M1 x) Nothing = M1 $ gzip pxy f x Nothing


-- | Nested leaf
-- | f b -> Maybe (f b) -> g b
instance {-# OVERLAPPABLE #-}
  (constr b)
  => GZip (constr :: * -> Constraint) (K1 c (f b)) (K1 c (g b)) f g where
  gzip _ fxn (K1 fb) (Just (K1 fb2)) = K1 $ fxn fb (Just fb2)


-----------------------------------------------
-- | Nested HKD Case (Identity special case)


-- | Nested leaf
-- | b -> Maybe b -> g b
instance
  (constr b)
  => GZip (constr :: * -> Constraint) (K1 c  b) (K1 c (g b)) Identity g where
  gzip _ fxn (K1 ib) (Just (K1 ib2)) = K1 $ fxn (Identity ib) (Just $ Identity ib2)
  gzip _ fxn (K1 ib) Nothing         = K1 $ fxn (Identity ib) Nothing
