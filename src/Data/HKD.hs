{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.HKD
  ( module Data.HKD
  , gnhoist
  , gnsequence
  , gnsequencebr
  , gnfold
  , gndefault
  , Annotate(..)
  ) where

import           Data.HKD.GHoist
import           Data.HKD.GFold
import           Data.HKD.GTraverse
import           Data.Functor.Identity
import           Control.Compose((:.)(..), unO)
import           Control.Monad.State
import           GHC.Generics
import           GHC.Exts(Constraint)
import           Data.Typeable

import           Data.Text(Text)

type family HKD f a where
  HKD Identity a = a
  HKD f a = f a

class Empty x
instance Empty x

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


--instance NothingOut'   


skeleton ::
  ( Generic (a Maybe)
  , GDefault Empty (Rep (a Maybe)) Maybe
  ) => a Maybe
skeleton = gndefault (Proxy :: Proxy Empty) Nothing


validate ::
  ( Generic (a Maybe)
  , Generic (a (Maybe :. Ident'))
  , Generic (a Ident')
--  , Generic (a Identity)  
  , GHoist Empty (Rep (a Maybe)) (Rep (a (Maybe :. Ident'))) Maybe (Maybe :. Ident')
--  , GHoist Empty (Rep (a Ident')) (Rep (a Identity)) Ident' Identity
  , GTraverse (Rep (a (Maybe :. Ident'))) (Rep (a Ident')) Maybe
  )
  => a Maybe -> Maybe (a Ident')
validate  =   gnsequence
            . gnhoist (Proxy :: Proxy Empty) fxn
  where
    fxn :: Maybe b -> (Maybe :. Ident') b
    fxn = O . fmap (Ident' . Identity)




nestLabel :: forall a f f_an st_f_an st .
  ( f_an ~ (Annotate [Int] :. f)
  , st_f_an ~ (State st :. (Annotate [Int] :. f))
  , Generic (a f)
  , Generic (a f_an)
  , Generic (a st_f_an)
  , GTraverse (Rep (a st_f_an)) (Rep (a f_an)) (State st)
  , GHoist Empty (Rep (a f)) (Rep (a st_f_an)) f st_f_an
  , Functor f
--   , Foldable f
  , st ~ (Int, [Int])
  )
  => a f -> a (Annotate [Int] :. f)
nestLabel x = y 
  where

    x' :: a (State st :. (Annotate [Int] :. f))
    x' = gnhoist (Proxy :: Proxy Empty) pathAn x
    
    y :: a (Annotate [Int] :. f)
    y = fst $ (`runState` ((0, []) :: st)) m

    m :: State st (a (Annotate [Int] :. f))
    m = gnsequencebr brkt x'

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
      
      
    --pathAn Nothing = O $ return $ O $ (Nothing :: f (Annotate [Int] c))
    -- pathAn (Just x) = O $ do
    --   ((_, path) :: st) <- get
    --   return (O $ Just (Annotate path x))

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


