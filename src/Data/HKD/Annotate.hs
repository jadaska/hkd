{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
module Data.HKD.Annotate where

import           GHC.Generics


-- | annotation type
data Annotate a b = Annotate a b deriving (Generic, Functor, Foldable, Show)

unAnnotate :: Annotate a b -> (a, b)
unAnnotate (Annotate a b) = (a, b)

-- | an empty functor
data NullF a = Null deriving (Generic, Functor, Foldable, Show)
