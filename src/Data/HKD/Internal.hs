{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.HKD.Internal where

import Data.Functor.Identity
import GHC.Exts(Constraint)
import GHC.Generics

type family HKD f a where
  HKD Identity a = a
  HKD f a = f a

type HKDChildConstr (ff :: * -> *) (a :: (* -> *) -> *) (c :: * -> Constraint) =
  ChildConstr ff (Rep (a Maybe)) c

type HKDLeafConstr (a :: (* -> *) -> *) (c :: * -> Constraint) =
  LeafConstr (Rep (a Maybe)) c

type HKDInternalConstr (a :: (* -> *) -> *)
                       (c :: ((* -> *) -> *) -> Constraint) =
  InternalConstr (Rep (a Maybe)) c





type family ChildConstr (gg :: * -> *) (t :: * -> *) (c :: * -> Constraint) :: Constraint where
 ChildConstr gg V1 c = ()
 ChildConstr gg U1 c = ()
 ChildConstr gg (f :+: g) c = (ChildConstr gg f c, ChildConstr gg g c)
 ChildConstr gg (f :*: g) c = (ChildConstr gg f c, ChildConstr gg g c)
 ChildConstr gg Par1 c = ()
 ChildConstr gg (K1 i (ff (a ff))) c = c (a gg) -- reached a nested, internal node
 ChildConstr gg (K1 i (ff a)) c = c a -- nested leaf node
 ChildConstr gg (K1 i k) c = (c k) -- internal node
 ChildConstr gg (M1 i t f) c = ChildConstr gg f c

type family LeafConstr (t :: * -> *) (c :: * -> Constraint) :: Constraint where
 LeafConstr V1 c = ()
 LeafConstr U1 c = ()
 LeafConstr (f :+: g) c = (LeafConstr f c, LeafConstr g c)
 LeafConstr (f :*: g) c = (LeafConstr f c, LeafConstr g c)
 LeafConstr Par1 c = ()
 LeafConstr (K1 i (ff (a ff))) c = () -- reached a non-leaf node
 LeafConstr (K1 i (ff a)) c = c a -- a leaf node
 LeafConstr (K1 i k) c = () -- anything else, don't bother
 LeafConstr (M1 i t f) c = LeafConstr f c


type family InternalConstr (t :: * -> *)
                           (c :: ((* -> *) -> *) -> Constraint) :: Constraint where
 InternalConstr V1 c = ()
 InternalConstr U1 c = ()
 InternalConstr (f :+: g) c = (InternalConstr f c, InternalConstr g c)
 InternalConstr (f :*: g) c = (InternalConstr f c, InternalConstr g c)
 InternalConstr Par1 c = ()
 InternalConstr (K1 i (ff (a ff))) c = c a -- reached a nested, internal node
 InternalConstr (K1 i (ff a)) c = ()  -- nested leaf node
 InternalConstr (K1 i (a ff)) c = c a -- internal node
 InternalConstr (M1 i t f) c = InternalConstr f c
