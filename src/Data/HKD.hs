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
{-# LANGUAGE Arrows #-}

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
import qualified Data.Map as M
import           Data.Text(Text)
import           Control.Arrow
import           Control.Monad.Writer

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
pxyEmpty :: Proxy Empty
pxyEmpty = Proxy


skeleton ::
  ( Generic (a Maybe)
  , GDefault Empty (Rep (a Maybe)) Maybe
  ) => a Maybe
skeleton = gndefault (Proxy :: Proxy Empty) Nothing


validate ::
  ( Generic (a Maybe)
  , Generic (a (Maybe :. Ident'))
  , Generic (a Ident')
  , Generic (a Identity)  
  , GHoist Empty (Rep (a Maybe)) (Rep (a (Maybe :. Ident'))) Maybe (Maybe :. Ident')
  , GHoist Empty (Rep (a Ident')) (Rep (a Identity)) Ident' Identity
  , GTraverse (Rep (a (Maybe :. Ident'))) (Rep (a Ident')) Maybe
  )
  => a Maybe -> Maybe (a Identity)
validate = fmap (gnhoist pxyEmpty unIdent') . gnsequence . gnhoist pxyEmpty fxn
  where
    fxn :: Maybe b -> (Maybe :. Ident') b
    fxn = O . fmap (Ident' . Identity)




type Labelable a f =
  (
-- f_an ~ (Annotate [Int] :. f)
--   , st_an_f ~ (State st :. (Annotate [Int] :. f))
    Generic (a f)
  , Generic (a (Annotate [Int] :. f))
  , Generic (a (State (Int, [Int]) :. (Annotate [Int] :. f)))
  , GTraverse (Rep (a (State (Int, [Int]) :. (Annotate [Int] :. f))))
              (Rep (a (Annotate [Int] :. f)))
              (State (Int, [Int]))
  , GHoist Empty (Rep (a f))
                 (Rep (a (State (Int, [Int]) :. (Annotate [Int] :. f))))
                 f
                 (State (Int, [Int]) :. (Annotate [Int] :. f))
  , Functor f
  )

nestLabel :: forall a f f_an st_f_an st .
  ( Labelable a f 
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



type OverAnnotate a f g c
                  an_f an_g lbl_g lbl_an_f =
  ( an_f ~ (Annotate (Maybe c) :. f)
  , an_g ~ (Annotate (Maybe c) :. g)
  , lbl_g ~ (Annotate [Int] :. g)
  , lbl_an_f ~ (Annotate [Int] :. (Annotate (Maybe c) :. f))

  , Labelable a an_f
  , Labelable a g
  , Generic (a an_g)
  , Generic (a f)
  , Generic (a (Writer [([Int], c)] :. f))
  , GHoist Empty (Rep (a lbl_g)) (Rep (a an_g)) lbl_g an_g
  , GHoist Empty (Rep (a an_f)) (Rep (a f)) an_f f
  , GHoist Empty (Rep (a lbl_an_f))
                 (Rep (a (Writer [([Int], c)] :. f)))
                 lbl_an_f (Writer [([Int], c)] :. f)
  , GTraverse (Rep (a (Writer [([Int], c)] :. f)))
              (Rep (a f))
              (Writer [([Int], c)])
--   , GFold Empty (Rep (a lbl_an_f)) lbl_an_f [([Int], c)]
  )

overAnnotation :: forall p a f g c an_f an_g lbl_g lbl_an_f .
  ( Arrow p
  , OverAnnotate a f g c an_f an_g lbl_g lbl_an_f
  )
  => p (a f) (a g)
  -> p (a (Annotate (Maybe c) :. f)) (a (Annotate (Maybe c) :. g))
overAnnotation arrow = proc x -> do
  m <- arr M.fromList -< snd $ runWriter $ gnsequence $ gnhoist pxyEmpty outfxn (nestLabel x)
  y <- arrow -< dropAn x
  arr id -< addAn m y
  
  where
    outfxn :: (Annotate [Int] :. (Annotate (Maybe c) :. f)) z -> (Writer [([Int], c)] :. f) z -- [([Int], c)]
    outfxn (O (Annotate ix's (O (Annotate my fx)))) = O $ do
      case my of
        Just y  -> tell [(ix's, y)]
        Nothing -> return ()
      return fx
      
--    fldfxn (O (Annotate ix's (O (Annotate (Just y) fx)))) = tell [(ix's, y)] >> return fx

    dropAn :: a (Annotate (Maybe c) :. f) -> a f
    dropAn = gnhoist pxyEmpty (snd . unAnnotate . unO)

    addAn :: M.Map [Int] c -> a g -> a (Annotate (Maybe c) :. g)
    addAn m = gnhoist pxyEmpty fxn .  nestLabel
      where
        fxn :: (Annotate [Int] :. g) z -> (Annotate (Maybe c) :. g) z
        fxn (O (Annotate ix's gz)) = O (Annotate (M.lookup ix's m) gz)
      

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


