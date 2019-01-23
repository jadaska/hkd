{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

module Main where
import           GHC.Generics
import           GHC.Exts(Constraint)
import           Generics.OneLiner
import           Data.Functor.Identity
import Data.HKD
import Data.HKD.Internal
import Data.Text
import Data.Typeable
import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Compose ((:.)(..))
import           Data.Functor.Const
import           Generics.OneLiner
import           Data.Constraints.Utility

main :: IO ()
main = putStrLn "hello HKD"


data Person' f = Person
  { name :: HKD f Text
  , address :: Address' f
  , pets :: HKD f [Pet' f]
  } deriving (Generic)

deriving instance (Constraints (Person' f) Show)
  => Show (Person' f)

data Pet' f = Pet
  { species :: HKD f Species
  , petName :: HKD f Text
  , toy     :: HKD f (Toy' f)
  } deriving (Generic)

instance ( HKDChildConstr f Pet' (HasHKD f)
         , HKDChildConstr g Pet' (HasHKD g)
         , Functor f
         , GHoistable Empty Toy' f g
         ) => GHoistable Empty Pet' f g  where

-- instance GHoistable Empty Pet' Maybe (Annotate b) where

deriving instance (Constraints (Pet' f) Show)
  => Show (Pet' f)

data Species = Dog | Cat | Fish deriving (Generic, Eq, Show)

data Toy' f = Toy
  { toyName :: HKD f Text
  , squeaks :: HKD f Bool
  } deriving Generic


class (HKD f a ~ f a) => HasHKD f a
instance (HKD f a ~ f a) => HasHKD f a

instance ( HKDChildConstr f Toy' (HasHKD f)
         , HKDChildConstr g Toy' (HasHKD g)
         ) => GHoistable Empty Toy' f g  where

deriving instance (Constraints (Toy' f) Show)
  => Show (Toy' f)

data Address' f = Address
  { street  :: HKD f Text
  , zipcode :: HKD f Text
  , state   :: HKD f Text
  } deriving Generic

deriving instance (Constraints (Address' f) Show)
  => Show (Address' f)

person :: Person' Maybe
person = Person (Just "Jason") addr1 (Just [pet1, pet2])
addr1 = Address (Just "11732 Perry Street") Nothing (Just "CO")
pet1 = Pet (Just Dog) (Just "Loki") (Just (Toy Nothing (Just True)))
pet2 = Pet (Just Fish) (Just "Nemo") Nothing


completePet :: Pet' Maybe -> Pet' Maybe
completePet (Pet x y t) = Pet x y t'
  where
    t' = Just $ Toy (Just "ball") (Just False)

-- labelPet :: Pet' Maybe -> Pet' (Annotate (Maybe Int) :. Maybe)
-- labelPet = gnhoist pxyEmpty fxn . nestLabel
--   where
--     fxn :: (Annotate [Int] :. Maybe) z -> (Annotate (Maybe Int) :. Maybe) z
--     fxn (O (Annotate ix's (Just x))) = O $ Annotate (Just (sum ix's)) (Just x)
--     fxn (O (Annotate ix's Nothing))  = O $ Annotate Nothing Nothing





-- hasChar :: Char -> Person' Maybe -> [String]
-- hasChar c = gnfold (Proxy :: Proxy Show) fxn
--   where
--     fxn :: Show a => Maybe a -> [String]
--     fxn (Just x) = if c `elem` show x then [show x] else []
--     fxn Nothing = []

-- hasCharLvl :: forall monad .
--   (
--     monad ~ State Int
--   )
--   => Char -> Person' Maybe -> [(String, Int)] -- Person' (Maybe :. Annotate Int)
-- hasCharLvl c p = gnfold (Proxy :: Proxy Show) lvlfxn p''
--   where
--     lvlfxn :: Show c => (Maybe :. Annotate Int) c -> [(String, Int)]
--     lvlfxn (O Nothing) = []
--     lvlfxn (O (Just (Annotate i x))) = if c `elem` show x then [(show x, i)] else []

--     p' :: Person' (monad :. (Maybe :. Annotate Int))
--     p' = gnhoist (Proxy :: Proxy Empty) lvlAn p

--     p'' :: Person' (Maybe :. Annotate Int)
--     p'' = fst $ (`runState` (0 :: Int)) m

--     m :: monad (Person' (Maybe :. Annotate Int))
--     m = gnsequencebr brkt p'

--     brkt :: monad (monad a) -> monad a
--     brkt mmx = do
--       mx <- mmx
--       lvl <- get
--       put (lvl + 1)
--       x <- mx
--       put lvl
--       return x

--     lvlAn :: Maybe c -> (monad :. (Maybe :. Annotate Int)) c
--     lvlAn Nothing = O $ return $ O $ (Nothing :: Maybe (Annotate Int c))
--     lvlAn (Just x) = O $ do
--       (lvl :: Int) <- get
--       return (O $ Just (Annotate lvl x))



-- instance (Show a, Show b) => Show ((Maybe :. Annotate a) b) where
--   show (O (Just (Annotate a b))) = show b <> "@" <> show b
