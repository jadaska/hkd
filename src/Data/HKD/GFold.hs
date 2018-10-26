{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
--{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
--{-# LANGUAGE InstanceSigs #-}
--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

module Data.HKD.GFold where

import           GHC.Generics
import           GHC.Exts(Constraint)
import           Data.Monoid
import           Control.Monad
import           Data.Typeable
import           Data.Foldable


gnfold :: forall a f constr m .  
  (
      Generic (a f)
    , GFold constr (Rep (a f)) f m
  )
  => Proxy constr
  -> (forall b . constr b => f b -> m)
  -> a f -> m
gnfold pxyc f = gfold (Proxy :: Proxy f) pxyc f . from 


-- | Generic Fold
class GFold (constr :: * -> Constraint) i f m where
  gfold :: Proxy f -> Proxy constr -> (forall b . constr b => f b -> m) -> i p -> m

instance (Monoid m, GFold constr i f m, GFold constr i' f m) => GFold constr (i :+: i') f m where
    gfold p1 p2  fxn (L1 l) = gfold p1 p2 fxn l
    gfold p1 p2 fxn (R1 r) = gfold p1 p2 fxn r

instance (Monoid m, GFold constr i f m, GFold constr i' f m) => GFold constr (i :*: i') f m where
    gfold p1 p2 fxn (l :*: r) = mappend (gfold p1 p2 fxn l) (gfold p1 p2 fxn r)

instance Monoid m => GFold constr V1 f m where
    gfold _ _ _ = mempty

instance {-# OVERLAPPABLE #-} (Monoid m, GFold constr i f m) => GFold constr (M1 _a _b i) f m where
  gfold p1 p2 fxn (M1 x) = gfold p1 p2 fxn x

-- | Nested HKD Case


-- | Internal node
-- | a f -> m
instance 
  ( Generic (a f)
  , GFold constr (Rep (a f)) f m
  ) => GFold constr (K1 c (a f)) f m where
  gfold pxyf pxyc fxn (K1 af) = gnfold pxyc fxn af

-- | Nested leaf
-- | f b -> m
instance {-# OVERLAPPABLE #-}
  (constr b)
  => GFold (constr :: * -> Constraint) (K1 c (f b)) f m where
  gfold _ _ fxn (K1 fb) = fxn fb

-- | Nested Internal node
-- | f a f -> m
instance {-# OVERLAPS #-}
  ( Generic (a f)
  , Functor f
  , Foldable f
  , GFold constr (Rep (a f)) f m
--  , constr (a f)
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
  gfold pxyf pxyc fxn (K1 faf) = fold fm
    where
      fm :: f m
      fm = gnfold pxyc fxn <$> faf

-- | Nested container of Internal nodes
-- | f (t (a f)) -> m
instance {-# OVERLAPPING #-}
  ( Generic (a f)
  , Functor f
  , Functor t
  , Foldable t
  , GFold constr (Rep (a f)) f m
  , Foldable f
  , Monoid m  
  ) => GFold (constr :: * -> Constraint) (K1 c (f (t (a f)))) f m where
  gfold pxyf pxyc fxn (K1 ftaf) = fold fm
    where
      ftm = fmap (fmap (gnfold pxyc fxn :: _ -> m)) ftaf
      fm  = fold <$> ftm
      

-- -- | Container of nested leaves
-- -- | t (f b) -> m
instance {-# OVERLAPPING #-}
  ( Functor f
  , Functor t
  , Foldable t
  , constr b
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (f b))) f m where
  gfold _ _ fxn (K1 tfb) = fold $ fmap fxn tfb


-- | Container of internal nodes
-- | t (a f) -> m
instance {-# OVERLAPS #-}
  ( Generic (a f)
  , Functor t
  , Foldable t
  , Monoid m
  , GFold constr (Rep (a f)) f m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (a f))) f m where
  gfold pxyf pxyc fxn (K1 taf) = fold tm
    where
      tm = fmap (gnfold pxyc fxn) taf

-- | Container of internal nodes
-- | t (f (a f)) -> m
instance
  ( Generic (a f)
  , Functor f
  , Functor t
  , Foldable t
  , Foldable f
  , GFold constr (Rep (a f)) f m
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (f (a f)))) f m where
  gfold pxyf pxyc (fxn :: forall b . constr b => f b -> m) (K1 tfaf) = fold tm
    where
      tfm :: t (f m)
      tfm = fmap (fmap (gnfold pxyc fxn :: _ -> m)) tfaf

      tm :: t m
      tm = fmap fold tfm
      


-- | Generic Default
gndefault :: forall a f constr . 
  (
      Generic (a f)
    , GDefault constr (Rep (a f)) f
  )
  => Proxy constr
  -> (forall b . constr b => f b)
  -> a f
gndefault pxy f = to $ gdefault (Proxy :: Proxy f) pxy f


class GDefault (constr :: * -> Constraint) o f where
  gdefault :: Proxy f -> Proxy constr -> (forall b . constr b => f b) ->  o p

instance {-# OVERLAPPABLE #-}
  ( GDefault constr i f
  , GDefault constr i' f
  ) => GDefault constr (i :+: i') f where
    gdefault pf pxy f = L1 $ gdefault pf pxy f

instance
  ( GDefault constr i f
  , GDefault constr i' f)
  => GDefault constr (i :*: i') f where
    gdefault pf pxy f =  gdefault pf pxy f :*: gdefault pf pxy f

instance
  ( GDefault constr i f)
  => GDefault constr (M1 _a _b i) f where
  gdefault pf pxy f = M1 $ gdefault pf pxy f

instance GDefault constr V1 f where
  gdefault _ _ _  = undefined

-- | HKD Nesting


-- | Internal node
-- | a f
instance
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  )
  => GDefault constr (K1 c (a f)) f where
    gdefault pf pxy f = K1 $ gndefault pxy f


-- | Nested leaf
-- | f b
instance {-# OVERLAPPABLE #-}
  (constr b) => GDefault constr (K1 c (f b)) f where
    gdefault pf pxy = K1


-- | Container of Internal nodes
-- | t (a f)
instance
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  , Applicative t
  )
  => GDefault constr (K1 c (t (a f))) f where
    gdefault pf pxy f = K1 $ pure $ gndefault pxy f

-- | Nested Internal node
-- | t (a f)
instance
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  , Applicative f
  )
  => GDefault constr (K1 c (f (a f))) f where
    gdefault pf pxy f = K1 $ pure $ gndefault pxy f



-- | Double Nested/Container Internal node
-- | g (a f)
instance {-# OVERLAPPING #-}
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  , Applicative f
  , Applicative g
  )
  => GDefault constr (K1 c (g (f (a f)))) f where
    gdefault pf pxy f = K1 $ pure $ pure $ gndefault pxy f

-- | Double Nested/Container Internal node
-- | g (a f)
instance {-# OVERLAPPING #-}
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  , Applicative f
  , Applicative g
  )
  => GDefault constr (K1 c (f (g (a f)))) f where
    gdefault pf pxy f = K1 $ pure $ pure $ gndefault pxy f



    
-- -- -- Maybe instance for Default


-- -- instance GDefault (K1 b (Maybe a)) where
-- --   gdefault = K1 Nothing
