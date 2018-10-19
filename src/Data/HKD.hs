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

module Data.HKD
  ( module Data.HKD
  , gnhoist
  , gnsequence
  , gnfold
  , gndefault
  
  ) where

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

class Empty x
instance Empty x

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


