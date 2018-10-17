{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.HKD where

import           Data.HKD.GHoist
import           Data.HKD.GFold
import           Data.HKD.GTraverse
import           Data.Functor.Identity
import           Control.Compose((:.)(..), unO)
import           GHC.Generics
import           GHC.Exts(Constraint)
import           Data.Typeable

import           Data.Text(Text)

type family HKD f a where
  HKD Identity a = a
  HKD f a = f a


data Person' f = Person
  { name :: HKD f Text
  , address :: HKD f (Address' f)
  , pets :: HKD f [Pet' f]
  } deriving (Generic)

deriving instance Show (Person' Identity)
deriving instance Show (Person' Maybe)

data Pet' f = Pet'
  { species :: f Species
  , petName :: f Text
  } deriving (Generic)

deriving instance Show (Pet' Identity)
deriving instance Show (Pet' Maybe)

data Species = Dog | Cat | Fish deriving (Generic, Eq, Show)

data Address' f = Address'
  { street :: f Text
  , zipcode :: f Text
  , state :: f Text
  } deriving Generic

deriving instance Show (Address' Identity)
deriving instance Show (Address' Maybe)

    


-- gntraverse :: forall (constr :: * -> Constraint) f g a  . 
--   ( Functor g
--   , Commute f g
--   , Generic (a g)
--   )
--   => Proxy (constr :: * -> Constraint)
--   -> (forall b . constr b => b -> f b)
--   -> a g
--   -> f (a g)
--  gntraverse pxyc fxn = gnsequence . gnhoist pxyc (fxn' (Proxy :: Proxy constr) fxn)
--   where
--     p :: Proxy constr
--     p = pxyc
--     fxn' :: Proxy (constr :: * -> Constraint)
--          -> (forall b . constr b => b -> f b)
--          -> (forall b . constr b => g b -> (f :. g) b)
--     fxn' _ fxn0 gb = O fgb
--       where
--         gfb = fmap fxn0 gb
--         fgb = commute gfb


