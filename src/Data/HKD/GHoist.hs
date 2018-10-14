{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.HKD.GHoist where

import Data.Functor.Identity
import GHC.Generics

import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Compose((:.)(..))


-- | Generic Hoist
class GHoist i o f g where
  ghoist :: i (f p) -> o (g p)

instance (GHoist i o f g, GHoist i' o' f g) => GHoist (i :+: i') (o :+: o') f g where
  ghoist (L1 l) = L1 $ ghoist l
  ghoist (R1 r) = R1 $ ghoist r  

instance (GHoist i o f g, GHoist i' o' f g) => GHoist (i :*: i') (o :*: o') f g where
  ghoist (l :*: r) = ghoist l :*: ghoist r
  
instance GHoist V1 V1 f g where
    ghoist = undefined

instance {-# OVERLAPPABLE #-} (GHoist i o f g) => GHoist (M1 _a _b i) (M1 _a' _b' o) f g where
  ghoist (M1 x) = M1 $ ghoist x

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


gnhoist :: forall a f g . 
  (
      GHoist (Rep (a f)) (Rep (a g)) f g
    , Generic (a f)
    , Generic (a g)
  ) => a f -> a g 
gnhoist = to . (ghoist :: _ (f _) -> _ (g _)) . from
