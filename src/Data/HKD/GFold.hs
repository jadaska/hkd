{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
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
import           Data.HKD.Annotate
import           Control.Compose ((:.)(..), unO)

type GFoldable constr a f m =
  ( Generic (a f)
  , GFold constr (Rep (a f)) f m
  )

gnfold :: forall a f constr m .  
  GFoldable constr a f m
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
--  , Foldable f
  , GFold constr (Rep (a f)) f m
  , constr (a f)
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
  gfold pxyf pxyc fxn (K1 faf) = fxn faf --fold fm
    -- where
    --   fm :: f m
    --   fm = gnfold pxyc fxn <$> faf


-- instance {-# OVERLAPS #-}
--   ( Generic (a f)
--   , Functor f
--   , Foldable f
--   , GFold constr (Rep (a f)) f m
-- --  , constr (a f)
--   , Monoid m
--   ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
--   gfold pxyf pxyc fxn (K1 faf) = fold fm
--     where
--       fm :: f m
--       fm = gnfold pxyc fxn <$> faf


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
instance {-# OVERLAPPABLE #-}
  ( Functor f
  , Functor t
  , Foldable t
  , constr b
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (f b))) f m where
  gfold _ _ fxn (K1 tfb) = fold $ fmap fxn tfb


-- | Container of internal nodes
-- | t (a f) -> m
instance {-# OVERLAPPING #-}
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
instance {-# OVERLAPS #-}
  ( Generic (a f)
  --, t ~ []
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


--------------
-- Temporary GFold that grabs all the leaves

type GFoldable2 constr a f m =
  ( Generic (a f)
  , GFold2 constr (Rep (a f)) f m
  )

gnfold2 :: forall a f constr m .  
  GFoldable2 constr a f m
  => Proxy constr
  -> (forall b . constr b => f b -> m)
  -> a f -> m
gnfold2 pxyc f = gfold2 (Proxy :: Proxy f) pxyc f . from 


-- | Generic Fold
class GFold2 (constr :: * -> Constraint) i f m where
  gfold2 :: Proxy f -> Proxy constr -> (forall b . constr b => f b -> m) -> i p -> m

instance (Monoid m, GFold2 constr i f m, GFold2 constr i' f m) => GFold2 constr (i :+: i') f m where
    gfold2 p1 p2  fxn (L1 l) = gfold2 p1 p2 fxn l
    gfold2 p1 p2 fxn (R1 r) = gfold2 p1 p2 fxn r

instance (Monoid m, GFold2 constr i f m, GFold2 constr i' f m) => GFold2 constr (i :*: i') f m where
    gfold2 p1 p2 fxn (l :*: r) = mappend (gfold2 p1 p2 fxn l) (gfold2 p1 p2 fxn r)

instance Monoid m => GFold2 constr V1 f m where
    gfold2 _ _ _ = mempty

instance {-# OVERLAPPABLE #-} (Monoid m, GFold2 constr i f m) => GFold2 constr (M1 _a _b i) f m where
  gfold2 p1 p2 fxn (M1 x) = gfold2 p1 p2 fxn x

-- | Nested HKD Case


-- | Internal node
-- | a f -> m
instance 
  ( Generic (a f)
  , GFold2 constr (Rep (a f)) f m
  ) => GFold2 constr (K1 c (a f)) f m where
  gfold2 pxyf pxyc fxn (K1 af) = gnfold2 pxyc fxn af

-- | Nested leaf
-- | f b -> m
instance {-# OVERLAPPABLE #-}
  (constr b)
  => GFold2 (constr :: * -> Constraint) (K1 c (f b)) f m where
  gfold2 _ _ fxn (K1 fb) = fxn fb

-- | Nested Internal node
-- | f a f -> m
instance {-# OVERLAPS #-}
  ( Generic (a f)
  , Functor f
  , Foldable f
  , GFold2 constr (Rep (a f)) f m
--  , constr (a f)
  , Monoid m
  ) => GFold2 (constr :: * -> Constraint) (K1 c (f (a f))) f m where
  gfold2 pxyf pxyc fxn (K1 faf) = fold fm
    where
       fm :: f m
       fm = gnfold2 pxyc fxn <$> faf


-- instance {-# OVERLAPS #-}
--   ( Generic (a f)
--   , Functor f
--   , Foldable f
--   , GFold constr (Rep (a f)) f m
-- --  , constr (a f)
--   , Monoid m
--   ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
--   gfold pxyf pxyc fxn (K1 faf) = fold fm
--     where
--       fm :: f m
--       fm = gnfold pxyc fxn <$> faf


-- | Nested container of Internal nodes
-- | f (t (a f)) -> m
instance {-# OVERLAPPING #-}
  ( Generic (a f)
  , Functor f
  , Functor t
  , Foldable t
  , GFold2 constr (Rep (a f)) f m
  , Foldable f
  , Monoid m  
  ) => GFold2 (constr :: * -> Constraint) (K1 c (f (t (a f)))) f m where
  gfold2 pxyf pxyc fxn (K1 ftaf) = fold fm
    where
      ftm = fmap (fmap (gnfold2 pxyc fxn :: _ -> m)) ftaf
      fm  = fold <$> ftm
      

-- -- | Container of nested leaves
-- -- | t (f b) -> m
instance {-# OVERLAPPABLE #-}
  ( Functor f
  , Functor t
  , Foldable t
  , constr b
  , Monoid m
  ) => GFold2 (constr :: * -> Constraint) (K1 c (t (f b))) f m where
  gfold2 _ _ fxn (K1 tfb) = fold $ fmap fxn tfb


-- | Container of internal nodes
-- | t (a f) -> m
instance {-# OVERLAPPING #-}
  ( Generic (a f)
  , Functor t
  , Foldable t
  , Monoid m
  , GFold2 constr (Rep (a f)) f m
  ) => GFold2 (constr :: * -> Constraint) (K1 c (t (a f))) f m where
  gfold2 pxyf pxyc fxn (K1 taf) = fold tm
    where
      tm = fmap (gnfold2 pxyc fxn) taf

-- | Container of internal nodes
-- | t (f (a f)) -> m
instance {-# OVERLAPS #-}
  ( Generic (a f)
  --, t ~ []
  , Functor f
  , Functor t
  , Foldable t
  , Foldable f
  , GFold2 constr (Rep (a f)) f m
  , Monoid m
  ) => GFold2 (constr :: * -> Constraint) (K1 c (t (f (a f)))) f m where
  gfold2 pxyf pxyc (fxn :: forall b . constr b => f b -> m) (K1 tfaf) = fold tm
    where
      tfm :: t (f m)
      tfm = fmap (fmap (gnfold2 pxyc fxn :: _ -> m)) tfaf

      tm :: t m
      tm = fmap fold tfm

---------------------------















      
type GDefaultable constr a f =
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  )

-- | Generic Default
gndefault :: forall a f constr . GDefaultable constr a f 
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
instance {-# OVERLAPS #-}
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  , Applicative t
  )
  => GDefault constr (K1 c (t (a f))) f where
    gdefault pf pxy f = K1 $ pure $ gndefault pxy f

instance {-# OVERLAPPING #-}
  ( Generic (a Maybe)
  , GDefault constr (Rep (a Maybe)) Maybe
  )
  => GDefault constr (K1 c (Maybe (a Maybe))) Maybe where
    gdefault pf pxy f = K1 $ pure $ gndefault pxy f

-- | Nested Internal node
-- | t (a f)
-- instance {-# OVERLAPPABLE #-}
--   ( Generic (a f)
--   , GDefault constr (Rep (a f)) f
--   , Applicative f
--   )
--   => GDefault constr (K1 c (f (a f))) f where
--     gdefault pf pxy f = K1 $ pure $ gndefault pxy f



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




-- | Generalize Catamorphism

type GCatable constr a f m =
  ( Generic (a f)
  , Generic (a (Annotate m :. NullF))
  , GCata constr (Rep (a f)) (Rep (a (Annotate m :. NullF))) f m
  )

-- | convert a value to an Annotation placeholder
-- This supports the recursion for generalize catamorphism
toAnPh :: a -> (Annotate a :. NullF) b
toAnPh x = O $ (Annotate x Null)

-- | retreive a value from the Annotation placeholder
fromAnPh :: (Annotate a :. NullF) b -> a
fromAnPh (O (Annotate x Null)) = x

gncata :: forall a g f constr m .  
  ( GCatable constr a f m
  , g ~ (Annotate m :. NullF)
  , Functor f
  , constr (a g)
  )
  => Proxy constr
  -> (forall b . constr b => f b -> m)
  -> f (a f) -> m
gncata pxyc f = h . fmap (gncata' pxyc f)
  where
    h :: f (a g) -> m
    h = f

gncata' :: forall a g f constr m .  
  ( GCatable constr a f m
  , g ~ (Annotate m :. NullF)
  )
  => Proxy constr
  -> (forall b . constr b => f b -> m)
  -> a f -> a g
gncata' pxyc f =
      to
    . (gcata (Proxy :: Proxy f)
             pxyc
             (Proxy :: Proxy m)
             f)  -- g :: _ (f _) -> _ ((Annotate m :. NullF) _))
    . from
  where
    -- g :: forall b . constr b => f b -> (Annotate m :. NullF) b
    -- g = toAnPh . f

-- | Generic Fold
class GCata (constr :: * -> Constraint) i o f m where
  gcata :: Proxy f
        -> Proxy constr
        -> Proxy m
        -> (forall b . constr b => f b -> m)
        -> i (f p)
        -> o ((Annotate m :. NullF) p)

instance (GCata constr i o f m, GCata constr i' o' f m)
 => GCata constr (i :+: i') (o :+: o') f m where
  gcata p1 p2 p3 fxn (L1 l) = L1 $ gcata p1 p2 p3 fxn l
  gcata p1 p2 p3 fxn (R1 r) = R1 $ gcata p1 p2 p3 fxn r

instance (Monoid m, GCata constr i o f m, GCata constr i' o' f m)
  => GCata constr (i :*: i') (o :*: o') f m where
     gcata p1 p2 p3 fxn (l :*: r) = (gcata p1 p2 p3 fxn l) :*: (gcata p1 p2 p3 fxn r)

instance GCata constr V1 V1 f m where
  gcata _ _ _ _  = undefined 


-- instance {-# OVERLAPPABLE #-} (Monoid m, GFold constr i f m) => GFold constr (M1 _a _b i) f m where
--   gfold p1 p2 fxn (M1 x) = gfold p1 p2 fxn x

-- -- | Nested HKD Case


-- | Internal node
-- | a f -> m
instance 
  ( Generic (a f)
  , Generic (a g)
  , g ~ (Annotate m :. NullF)
  , GCata constr (Rep (a f)) (Rep (a g)) f m
--  , constr (a f)
  ) => GCata constr (K1 c (a f)) (K1 c (a g)) f m where
  gcata pxyf pxyc pxym fxn (K1 af) = K1 $ gncata' pxyc fxn af

-- | Nested leaf
-- | f b -> m
instance {-# OVERLAPPABLE #-}
  (constr b, g ~ (Annotate m :. NullF))
  => GCata (constr :: * -> Constraint) (K1 c (f b)) (K1 c (g b)) f m where
  gcata _ _ _ fxn (K1 fb) = K1 $ toAnPh $ fxn fb

-- -- | Nested Internal node
-- -- | f a f -> m
-- instance {-# OVERLAPS #-}
--   ( Generic (a f)
--   , Functor f
-- --  , Foldable f
--   , GFold constr (Rep (a f)) f m
--   , constr (a f)
--   , Monoid m
--   ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
--   gfold pxyf pxyc fxn (K1 faf) = fxn faf --fold fm




    
-- -- -- Maybe instance for Default


-- -- instance GDefault (K1 b (Maybe a)) where
-- --   gdefault = K1 Nothing
