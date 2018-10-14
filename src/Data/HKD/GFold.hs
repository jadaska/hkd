{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.HKD.GFold where

import           GHC.Generics
import           Data.Monoid
import           Control.Monad

-- | Generic Fold
class GFold i m where
  gfold :: i p -> m

instance (Monoid m, GFold i m, GFold i' m) => GFold (i :+: i') m where
    gfold (L1 l) = gfold l
    gfold (R1 r) = gfold r

instance (Monoid m, GFold i m, GFold i' m) => GFold (i :*: i') m where
    gfold (l :*: r) = mappend (gfold l) (gfold r)

instance Monoid m => GFold V1 m where
    gfold _ = mempty

instance {-# OVERLAPPABLE #-} (Monoid m, GFold i m) => GFold (M1 _a _b i) m where
  gfold (M1 x) = gfold x

-- | Nested HKD Case
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







-- gnfold :: 
--   (
--       Generic a
--     , GFold (Rep a) m
--   )
--   => a -> m
-- gnfold = gfold . from 


-- -- | Generic Unfold
-- class GUnfold m o where
--     gunfold :: [m] -> Maybe (o p)

-- instance (GUnfold m i, GUnfold m i') => GUnfold m (i :+: i') where
--     gunfold m's = (L1 <$> gunfold m's) `mplus` (R1 <$> gunfold m's) 

-- instance (GUnfold m i, GUnfold m i') => GUnfold m (i :*: i') where
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

-- | Generic Default
class GDefault o where
  gdefault :: o p

instance {-# OVERLAPPABLE #-} (GDefault i, GDefault i') => GDefault (i :+: i') where
    gdefault = L1 gdefault

instance (GDefault i, GDefault i') => GDefault (i :*: i') where
    gdefault =  gdefault :*: gdefault

instance (GDefault i) => GDefault (M1 _a _b i) where
  gdefault = M1 gdefault

instance GDefault V1 where
  gdefault  = undefined

-- -- Maybe instance for Default

gndefault :: 
  (
      Generic a
    , GDefault (Rep a)
  )
  => a
gndefault = to gdefault

-- instance GDefault (K1 b (Maybe a)) where
--   gdefault = K1 Nothing
