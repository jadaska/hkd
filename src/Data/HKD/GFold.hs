{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}


module Data.HKD.GFold where

import           GHC.Generics
import           GHC.Exts(Constraint)
import           Data.Monoid
import           Control.Monad
import           Data.Typeable
import           Data.Foldable
import           Data.HKD.Annotate
import           Control.Compose ((:.)(..), unO)


----------------------------------------------------------------
-- Generic Fold
----------------------------------------------------------------

-- | Constraint synonym that indicates gnfold can be used
type GFoldable constr a f m =
  ( Generic (a f)
  , GFold constr (Rep (a f)) f m
  )

-- | Generic fold which operates by converting the
-- leaves of the HKD structure to a monoid and then
-- concatenating the results on the way up the tree.
-- For nested structures the 'f' must be Foldable
gnfold :: forall a f constr m .
  ( GFoldable constr a f m
  , Monoid m
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
  , Monoid m
  ) => GFold constr (K1 c (a f)) f m where
  gfold _ pxyc fxn (K1 af) = gnfold pxyc fxn af

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
  , Monoid m
  ) => GFold (constr :: * -> Constraint) (K1 c (f (a f))) f m where
  gfold _ pxyc fxn (K1 faf) = fold fm
    where
      fm :: f m
      fm = gnfold pxyc fxn <$> faf

----------------------------------------------------------------
-- Generic Default
----------------------------------------------------------------

-- | Constraint synonym that allows creation of a default
-- version of an HKD type
type GDefaultable constr a f =
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  )

-- | Create a default instance of an HKD type
gndefault :: forall a f constr . GDefaultable constr a f
  => Proxy constr
  -> (forall b . constr b => f b)
  -> a f
gndefault pxy f = to $ gdefault (Proxy :: Proxy f) pxy f


class GDefault (constr :: * -> Constraint) o f where
  gdefault :: Proxy f -> Proxy constr -> (forall b . constr b => f b) ->  o p

instance
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

-- | Internal node
-- | a f
instance
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  )
  => GDefault constr (K1 c (a f)) f where
    gdefault _ pxy f = K1 $ gndefault pxy f


-- | Nested leaf
-- | f b
instance
  (constr b) => GDefault constr (K1 c (f b)) f where
    gdefault _ _ = K1

----------------------------------------------------------------
-- Generic Catamorphism
----------------------------------------------------------------

-- Nested Internal node
-- t (a f)
instance
  ( Generic (a f)
  , GDefault constr (Rep (a f)) f
  , Applicative f
  )
  => GDefault constr (K1 c (f (a f))) f where
    gdefault _ pxy f = K1 $ pure $ gndefault pxy f

-- | Constraint synomym needed to use the
-- generic catamorphism which combines nested
-- HKD data types with an defined algebra
type GCatable constr a f m =
  ( Generic (a f)
  , Generic (a (Annotate m :. NullF))
  , GCata constr (Rep (a f)) (Rep (a (Annotate m :. NullF))) f m
  )


-- | Generic catamorphism
class GCata (constr :: * -> Constraint) i o f m where
  gcata :: Proxy f
        -> Proxy constr
        -> Proxy m
        -> (forall b . constr b => f b -> m)
        -> i (f p)
        -> o ((Annotate m :. NullF) p)


gncata :: forall a g f constr m .
  ( GCatable constr a f m
  , g ~ (Annotate m :. NullF)
  )
  => Proxy constr
  -> (forall b . constr b => f b -> m)
  -> a f -> a g
gncata pxyc f =
      to
    . (gcata (Proxy :: Proxy f)
             pxyc
             (Proxy :: Proxy m)
             f)
    . from


instance (GCata constr i o f m, GCata constr i' o' f m)
 => GCata constr (i :+: i') (o :+: o') f m where
  gcata p1 p2 p3 fxn (L1 l) = L1 $ gcata p1 p2 p3 fxn l
  gcata p1 p2 p3 fxn (R1 r) = R1 $ gcata p1 p2 p3 fxn r

instance (Monoid m, GCata constr i o f m, GCata constr i' o' f m)
  => GCata constr (i :*: i') (o :*: o') f m where
     gcata p1 p2 p3 fxn (l :*: r) = (gcata p1 p2 p3 fxn l) :*: (gcata p1 p2 p3 fxn r)

instance GCata constr V1 V1 f m where
  gcata _ _ _ _  = undefined



-- | Internal node - a f -> a (Annotate m :. NullF)
instance
  ( Generic (a f)
  , Generic (a g)
  , g ~ (Annotate m :. NullF)
  , GCata constr (Rep (a f)) (Rep (a g)) f m
  ) => GCata constr (K1 c (a f)) (K1 c (a g)) f m where
  gcata _ pxyc _ fxn (K1 af) = K1 $ gncata pxyc fxn af

-- | Nested leaf - f b -> m
instance
  (constr b, g ~ (Annotate m :. NullF))
  => GCata (constr :: * -> Constraint) (K1 c (f b)) (K1 c (g b)) f m where
  gcata _ _ _ fxn (K1 fb) = K1 $ toAnPh $ fxn fb

-- | Nested Internal node
-- | f a f -> m
instance
  ( Generic (a f)
  , Generic (a g)
  , Functor f
  , g ~ (Annotate m :. NullF)
  , constr (a g)
  , GCata constr (Rep (a f)) (Rep (a g)) f m

  ) => GCata constr (K1 c (f (a f))) (K1 c (g (a g))) f m where
  gcata _ pxyc _ fxn (K1 faf) = K1 $ toAnPh $ fxn fag
    where
      fag :: f (a g)
      fag = gncata pxyc fxn <$> faf


-- | convert a value to an Annotation placeholder
-- This supports the recursion for generalize catamorphism
toAnPh :: a -> (Annotate a :. NullF) b
toAnPh x = O $ (Annotate x Null)

-- | retreive a value from the Annotation placeholder
fromAnPh :: (Annotate a :. NullF) b -> a
fromAnPh (O (Annotate x Null)) = x




------------------------------------------------------------
-- Generic ToList
------------------------------------------------------------

-- | Constraint synomym needed to use the
-- generic gather operation which returns a list
-- of immediate child elements (not recursively down a
-- nested structure)
type GToListable constr a f m =
  ( Generic (a f)
  , GToList constr (Rep (a f)) f m
  )


-- | Generic ToList
class GToList (constr :: * -> Constraint) i f m where
  gtolist :: Proxy f
          -> Proxy constr
          -> (forall b . constr b => f b -> m)
          -> i (f p)
          -> [m]


gntolist :: forall a g f constr m .
  ( GToListable constr a f m
  )
  => Proxy constr
  -> (forall b . constr b => f b -> m)
  -> a f -> [m]
gntolist pxyc f = gtolist (Proxy :: Proxy f) pxyc f . from


instance (GToList constr i f m, GToList constr i' f m)
 => GToList constr (i :+: i') f m where
  gtolist p1 p2 fxn (L1 l) = gtolist p1 p2 fxn l
  gtolist p1 p2 fxn (R1 r) = gtolist p1 p2 fxn r

instance (Monoid m, GToList constr i f m, GToList constr i' f m)
  => GToList constr (i :*: i') f m where
     gtolist p1 p2 fxn (l :*: r) = (gtolist p1 p2 fxn l) <> (gtolist p1 p2 fxn r)

instance GToList constr V1 f m where
  gtolist _ _ _ _  = undefined



-- | Internal node - a f -> [m]
instance
  ( Generic (a f)
  , GToList constr (Rep (a f)) f m
  ) => GToList constr (K1 c (a f)) f m where
  gtolist _ pxyc fxn (K1 af) = gntolist pxyc fxn af

-- | Nested node - f b -> m
instance
  (constr b, g ~ (Annotate m :. NullF))
  => GToList (constr :: * -> Constraint) (K1 c (f b)) f m where
  gtolist _ _ fxn (K1 fb) = [fxn fb]
