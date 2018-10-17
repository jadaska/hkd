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
      Generic a
    , GFold constr (Rep a) f m
  )
  => Proxy f -> Proxy constr -> (forall b . constr b => f b -> m) -> a -> m
gnfold pxyf pxyc f = gfold pxyf pxyc f . from 


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
  gfold pxyf pxyc fxn (K1 af) = gnfold pxyf pxyc fxn af

-- | Nested leaf
-- | f b -> m
instance
  (constr b)
  => GFold (constr :: * -> Constraint) (K1 c (f b)) f m where
  gfold _ _ fxn (K1 fb) = fxn fb

-- | Nested Internal node
-- | f a f -> m
instance
  ( Generic (a f)
  , Functor f
  , GFold constr (Rep (a f)) f m
  , constr (a f)
  , constr m
  ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
  gfold pxyf pxyc fxn (K1 faf) = fxn fm
    where
      fm :: f m
      fm = gnfold pxyf pxyc fxn <$> faf

-- | Nested container of Internal nodes
-- | f (t (a f)) -> m
instance
  ( Generic (a f)
  , Functor f
  , Functor t
  , Foldable t
  , GFold constr (Rep (a f)) f m
  , constr m
  , Monoid m  
  ) => GFold (constr :: * -> Constraint) (K1 c (f (t (a f)))) f m where
  gfold pxyf pxyc fxn (K1 ftaf) = fxn fm
    where
      ftm = fmap (fmap (gnfold pxyf pxyc fxn :: _ -> m)) ftaf
      fm  = fold <$> ftm
      

-- | Container of nested leaves
-- | t (f b) -> m
instance
  ( Functor f
  , Functor t
  , Foldable t
  , constr b
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (f b))) f m where
  gfold _ _ fxn (K1 tfb) = fold $ fmap fxn tfb


-- | Container of internal nodes
-- | t (a f) -> m
instance
  ( Generic (a f)
  , Functor t
  , Foldable t
  , Monoid m
  , GFold constr (Rep (a f)) f m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (a f))) f m where
  gfold pxyf pxyc fxn (K1 taf) = fold tm
    where
      tm = fmap (gnfold pxyf pxyc fxn) taf

-- | Container of internal nodes
-- | t (f (a f)) -> m
instance
  ( Generic (a f)
  , Functor f
  , Functor t
  , Foldable t
  , constr m
  , GFold constr (Rep (a f)) f m
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (t (f (a f)))) f m where
  gfold pxyf pxyc (fxn :: forall b . constr b => f b -> m) (K1 tfaf) = fold tm
    where
      tfm :: t (f m)
      tfm = fmap (fmap (gnfold pxyf pxyc fxn :: _ -> m)) tfaf

      tm :: t m
      tm = fmap fxn tfm
      



-- instance {-# OVERLAPPABLE #-} 
--   (
--       GFold (Rep (g (ff :: * -> *))) m 
--     , Generic (g ff)
--   ) => GFold (K1 a (g ff)) m where
--     gfold (K1 k) = gnfold k
--     {-# INLINE gfold #-}

-- instance {-# OVERLAPPABLE #-} (   

--       Monoid m
--     , GFold (Rep (g (ff :: * -> *))) m 
--     , Generic (g ff)
--   ) => GFold (K1 _a [g ff]) m where
--     gfold (K1 x) = foldMap gnfold x
--     {-# INLINE gfold #-}



-- instance {-# OVERLAPPABLE #-} (   

--       Monoid m
--     , GFold (Rep (g (ff :: * -> *))) m 
--     , Generic (g ff)
--   ) => GFold (M1 _a _b (K1 _a [g ff])) m where
--     gfold (M1 (K1 x)) = foldMap gnfold x
--     {-# INLINE gfold #-}    

-- instance {-# OVERLAPPABLE #-} 
--   (
--       GFold (Rep (g (ff :: * -> *))) m 
--     , Generic (g ff)
--   ) 
--   => GFold (K1 a (g ff)) m where
--     gfold (K1 k) = gnfold k
--     {-# INLINE gfold #-}




-- instance (
--     GFold (Rep g) m 
--   , Generic g 
--   ) => GFold (K1 a g) m where
--   gfold (K1 k) = gnfold k
--   {-# INLINE gfold #-}








-- -- | Generic Unfold
-- class GUnfold m o where
--     gunfold :: [m] -> Maybe (o p)

-- instance (GUnfold m i, GUnfold m i') => GUnfold m (i :+: i') where
--     gunfold m's = (L1 <$> gunfold m's) `mplus` (R1 <$> gunfold m's) 

-- instance (GUnfold m , GUnfold m i') => GUnfold m (i :*: i') where
--     gunfold (m:rest) =  do 
--         l <- gunfold [m]
--         r <- gunfold rest
--         return $ l :*: r 
--     gunfold [] = mzero

-- instance (GUnfold m i) => GUnfold m (M1 _a _b i) where
--   gunfold m's = M1 <$> gunfold m's


-- instance  GUnfold m V1 where
--     gunfold  = undefined

-- gnunfold :: 
--   (
--       Generic a
--     , GUnfold m (Rep a)
--   )
--   => [m] -> Maybe a
-- gnunfold = fmap to . gunfold

-- -- | Generic Default
-- class GDefault o where
--   gdefault :: o p

-- instance {-# OVERLAPPABLE #-} (GDefault i, GDefault i') => GDefault (i :+: i') where
--     gdefault = L1 gdefault

-- instance (GDefault i, GDefault i') => GDefault (i :*: i') where
--     gdefault =  gdefault :*: gdefault

-- instance (GDefault i) => GDefault (M1 _a _b i) where
--   gdefault = M1 gdefault

-- instance GDefault V1 where
--   gdefault  = undefined

-- -- -- Maybe instance for Default

-- gndefault :: 
--   (
--       Generic a
--     , GDefault (Rep a)
--   )
--   => a
-- gndefault = to gdefault

-- -- instance GDefault (K1 b (Maybe a)) where
-- --   gdefault = K1 Nothing
