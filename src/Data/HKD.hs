{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE DefaultSignatures #-}
module Data.HKD
  ( module Data.HKD
  , hkdhoist
  , hkdsequence
  , hkdsequencebr
  , hkdfold
  , hkddefault
  , HKDSequence
  , HKDHoist
  , HKDFold
  , HKDDefault
  , HKDZip
  , Annotate (..)
  , unAnnotate
  ) where

import           Data.Constraints.Utility
import           Data.HKD.Annotate
import           Data.HKD.Hoist
import           Data.HKD.Fold
import           Data.HKD.Traverse
import           Data.HKD.Zip
import           Data.Functor.Identity
import           Control.Compose((:.)(..), unO)
import           Control.Monad.State
import           GHC.Generics
import           GHC.Exts(Constraint)
import           Data.Typeable
import qualified Data.Map as M
import           Data.Text(Text)
import           Control.Arrow
import           Control.Monad.Writer

type family HKD f a where
  HKD Identity a = a
  HKD f a = f a

data HKDNode = HKDInternal | HKDLeaf

type family HKDNodeType (a :: *) where
  HKDNodeType (b (f :: * -> *)) = HKDInternal
  HKDNodeType (t (b (f :: * -> *))) = HKDInternal
  HKDNodeType (t (f (b (f :: * -> *)))) = HKDInternal
  HKDNodeType b = HKDLeaf

class NothingOut  a where
  nothingOut :: Maybe a -> (Maybe :. Annotate Bool) a

instance (HKDNodeType a ~ flag, NothingOut' flag a) => NothingOut a where
  nothingOut = nothingOut' (Proxy :: Proxy flag)

class NothingOut' (flag :: HKDNode) a  where
  nothingOut' :: Proxy flag -> Maybe a -> (Maybe :. Annotate Bool) a

instance NothingOut' 'HKDInternal a where
  nothingOut' _ x = O $ fmap (Annotate False) x

instance NothingOut' 'HKDLeaf a where
  nothingOut' _ x = O $ fmap (Annotate True) x


class IsHKDLeaf a where
  isHKDLeaf :: a -> Bool

instance (HKDNodeType a ~ flag, IsHKDLeaf' flag a) => IsHKDLeaf a where
  isHKDLeaf x = isHKDLeaf' (Proxy :: Proxy flag) x

class IsHKDLeaf' (flag :: HKDNode) a where
  isHKDLeaf' :: Proxy flag -> a -> Bool

instance IsHKDLeaf' 'HKDLeaf a where
  isHKDLeaf' _ _ = True
  {-# INLINE isHKDLeaf' #-}

instance IsHKDLeaf' 'HKDInternal a where
  isHKDLeaf' _ _ = False
  {-# INLINE isHKDLeaf' #-}


pxyEmpty :: Proxy Empty
pxyEmpty = Proxy


class HKDSkeleton a where
  hkdskeleton :: a Maybe

  default hkdskeleton ::
    ( Generic (a Maybe)
    , HKDDefault Empty Maybe a
    )
    => a Maybe
  hkdskeleton = hkddefault (Proxy :: Proxy Empty) Nothing

class HKDValidate a where
  hkdvalidate :: a Maybe -> Maybe (a Identity)

  default hkdvalidate ::
    ( HKDHoist Empty Maybe (Maybe :. Identity) a
    , HKDSequence Maybe Identity a
    )
    => a Maybe -> Maybe (a Identity)
  hkdvalidate = hkdsequence . hkdhoist pxyEmpty fxn

    where
      fxn :: Maybe b -> (Maybe :. Identity) b
      fxn = O . fmap Identity

-- type GValidateable a =
--   ( GHoistable Empty a Maybe (Maybe :. Ident')
--   , GHoistable Empty a Ident' Identity
--   , GSequenceable a Maybe Ident'
--   )

-- validate :: GValidateable a
--   => a Maybe
--   -> Maybe (a Identity)
-- validate = fmap (gnhoist pxyEmpty unIdent') . gnsequence . gnhoist pxyEmpty fxn
--   where
--     fxn :: Maybe b -> (Maybe :. Ident') b
--     fxn = O . fmap (Ident' . Identity)

type LblSt = State (Int, [Int])
type PathAn = Annotate [Int]

class HKDLabel f b a where

  dropAn :: a (Annotate b :. f) -> a f
  fieldLabel :: (Maybe String -> b) -> a f -> a (Annotate b :. f)

  default dropAn :: (HKDHoist Empty (Annotate b :. f) f a)
    => a (Annotate b :. f) -> a f
  dropAn = hkdhoist pxyEmpty (snd . unAnnotate . unO)

  default fieldLabel :: HKDHoist Empty f (Annotate b :. f) a
    => (Maybe String -> b) -> a f -> a (Annotate b :. f)
  fieldLabel g = hkdhoist' pxyEmpty Nothing fxn
    where
      fxn :: forall c . Maybe String -> f c -> (Annotate b :. f) c
      fxn ms fx = O $ Annotate (g ms) fx

class HKDNestLabel f a where

  nestLabel :: a f -> a (Annotate [Int] :. f)

  default nestLabel :: forall st .
    ( st ~ (Int, [Int])
    , Functor f
    , HKDHoist Empty f (LblSt :. (PathAn :. f)) a
    , HKDSequence LblSt (PathAn :. f) a
    )
    => a f -> a (Annotate [Int] :. f)
  nestLabel x = y
    where
      x' :: a (State st :. (Annotate [Int] :. f))
      x' = hkdhoist (Proxy :: Proxy Empty) pathAn x

      y :: a (Annotate [Int] :. f)
      y = fst $ (`runState` ((0, []) :: st)) m

      m :: State st (a (Annotate [Int] :. f))
      m = hkdsequencebr brkt x'

      brkt :: State st (State st b) -> State st b
      brkt mmx = do
        mx <- mmx
        (n, path) <- get
        put (0, n : path)
        x <- mx
        put (n, path)

        return x

      pathAn :: f c -> (State st :. (Annotate [Int] :. f)) c
      pathAn fc = O $ do
        ((n, path) :: st) <- get
        put (n+1, path)
        return $ O $ Annotate ((n+1):path) fc


type An c = Annotate c

-- type OverAnnotate a f g c =
--   ( GLabelable a (An (Maybe c) :. f)
--   , GLabelable a g
--   , GHoistable Empty a (An [Int] :. g) (An (Maybe c) :. g)
--   , GHoistable Empty a (An (Maybe c) :. f) f
--   , GHoistable Empty a (An [Int] :. (An (Maybe c) :. f)) (Writer [([Int], c)] :. f)
--   , GSequenceable a (Writer [([Int], c)]) f
--   )

class OverAnnotate f g c a where

  overAnnotation :: forall p . (Arrow p)
    => p (a f) (a g)
    -> p (a (Annotate (Maybe c) :. f)) (a (Annotate (Maybe c) :. g))

  default overAnnotation :: forall p .
    ( Arrow p
    , HKDNestLabel g a
    , HKDNestLabel (Annotate (Maybe c) :. f) a
    , HKDHoist Empty (An [Int] :. (An (Maybe c) :. f)) (Writer [([Int], c)] :. f) a
    , HKDHoist Empty (An (Maybe c) :. f) f a
    , HKDHoist Empty (An [Int] :. g) (An (Maybe c) :. g) a
    , HKDSequence (Writer [([Int], c)]) f a
    , HKDLabel f (Maybe c) a
    )
    => p (a f) (a g)
    -> p (a (Annotate (Maybe c) :. f)) (a (Annotate (Maybe c) :. g))
  overAnnotation arrow = proc x -> do
    m <- arr M.fromList -< snd $ runWriter $ hkdsequence $ hkdhoist pxyEmpty outfxn (nestLabel x)
    y <- arrow -< dropAn x
    arr id -< addAn m y

    where
      outfxn :: (Annotate [Int] :. (Annotate (Maybe c) :. f)) z -> (Writer [([Int], c)] :. f) z
      outfxn (O (Annotate ix's (O (Annotate my fx)))) = O $ do
        case my of
          Just y  -> tell [(ix's, y)]
          Nothing -> return ()
        return fx

      addAn :: M.Map [Int] c -> a g -> a (Annotate (Maybe c) :. g)
      addAn m = hkdhoist pxyEmpty fxn .  nestLabel
        where
          fxn :: (Annotate [Int] :. g) z -> (Annotate (Maybe c) :. g) z
          fxn (O (Annotate ix's gz)) = O (Annotate (M.lookup ix's m) gz)



-- data Diff a = Same a | Different (Maybe a) a deriving (Functor, Show)

-- gdiff :: forall a .
--   ( GZippable Eq a Identity Diff
--   )
--   => a Identity
--   -> a Identity
--   -> a Diff
-- gdiff x y = gnzip (Proxy :: Proxy Eq) fxn x (Just y)
--   where
--     fxn :: Eq b => Identity b -> Maybe (Identity b) -> Diff b
--     fxn (Identity x) my =
--       case my of
--         (Just (Identity y)) -> if x == y then Same x else Different (Just y) x
--         Nothing  -> Different Nothing x

-- gdiff :: forall a .
--   ( GZippable Eq a Maybe (Diff :. Maybe)
--   )
--   => a Maybe
--   -> a Maybe
--   -> a (Diff :. Maybe)
-- gdiff x y = gnzip (Proxy :: Proxy Eq) fxn x (Just y)
--   where
--     fxn :: Eq b => Maybe b -> Maybe (Maybe b) -> (Diff :. Maybe) b
--     fxn (Just x) mmy = O $
--       case join mmy of
--         (Just y) -> if x == y then Same (Just x) else Different (Just (Just y)) (Just x)
--         Nothing  -> Different Nothing (Just x)
--     fxn Nothing mmy = O $
--       case join mmy of
--         (Just y) -> Different mmy Nothing
--         Nothing  -> Same Nothing
