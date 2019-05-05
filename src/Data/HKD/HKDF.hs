{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Data.HKD.HKDF where

import GHC.Exts (IsList(..))

newtype HKDF (t :: * -> *) (a :: (* -> *) -> *) (f :: * -> *)
  = HKDF {unHkdF :: t (a f)}

instance IsList (t (a f)) => IsList (HKDF t a f) where
  type Item (HKDF t a f) = Item (t (a f))
  fromList xs = HKDF $ fromList xs
  toList (HKDF taf) = toList taf

instance Show (t (a f)) => Show (HKDF t a f) where
  show (HKDF taf) = show taf
