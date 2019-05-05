{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedLists #-}
-- {-# LANGUAGE OverlappingInstances #-}


module Main where
import           GHC.Generics
import           Data.Functor.Identity
import           Data.Constraints.Utility
import Data.HKD
import           Data.HKD.Traverse (Commute)
import           Data.HKD.HKDF
import Data.Text
import Data.Typeable
import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Compose ((:.)(..))
import           Data.Functor.Const

main :: IO ()
main = putStrLn "hello HKD"


data Person' f = Person
  { name :: f Text
  , address :: Address' f
  , pets :: f (HKDF [] Pet' f)
  } deriving (Generic)

deriving instance Show (Person' Identity)
deriving instance Show (Person' Maybe)
deriving instance Show a => Show (Person' (Annotate a :. Maybe))
deriving instance (Functor f, Generic (Person' f), Generic (Person' g))
  => HKDHoist Empty f g Person'
deriving instance (Commute f g, Functor g, Monad f, Generic (Person' f), Generic (Person' g))
  => HKDSequence f g Person'
deriving instance (Commute LblSt f, Functor f) => HKDNestLabel f Person'


data Pet' f = Pet
  { species :: f Species
  , petName :: f Text
  , toy     :: f (Toy' f)
  } deriving (Generic)

deriving instance Show (Pet' Identity)
deriving instance Show (Pet' Maybe)
deriving instance Show a => Show (Pet' (Annotate a :. Maybe))
deriving instance (Functor f, Generic (Pet' f), Generic (Pet' g)) => HKDHoist Empty f g Pet'
deriving instance (Commute f g, Functor g, Monad f, Generic (Pet' f), Generic (Pet' g)) => HKDSequence f g Pet'
deriving instance (Commute LblSt f, Functor f) => HKDNestLabel f Pet'

data Species = Dog | Cat | Fish deriving (Generic, Eq, Show)

data Toy' f = Toy
  { toyName :: f Text
  , squeaks :: f Bool
  } deriving Generic

deriving instance Show (Toy' Maybe)
deriving instance Show (Toy' Identity)
deriving instance Show a => Show (Toy' (Annotate a :. Maybe))
deriving instance (Generic (Toy' f), Generic (Toy' g)) => HKDHoist Empty f g Toy'
deriving instance (Applicative f, Generic (Toy' f)) => HKDSequence f g Toy'
deriving instance (Functor f) => HKDNestLabel f Toy'


data Address' f = Address
  { street  :: f Text
  , zipcode :: f Text
  , state   :: f Text
  } deriving Generic

deriving instance Show (Address' Identity)
deriving instance Show (Address' Maybe)
deriving instance Show a => Show (Address' (Annotate a :. Maybe))
deriving instance (Functor f, Generic (Address' f), Generic (Address' g))
  => HKDHoist Empty f g Address'
deriving instance (Commute f g, Functor g, Monad f, Generic (Address' f), Generic (Address' g))
  => HKDSequence f g Address'
deriving instance (Commute LblSt f, Functor f) => HKDNestLabel f Address'



person :: Person' Maybe
person = Person (Just "Jason") addr1 (Just [pet1, pet2])
addr1 = Address (Just "11732 Perry Street") Nothing (Just "CO")
pet1 = Pet (Just Dog) (Just "Loki") (Just (Toy Nothing (Just True)))
pet2 = Pet (Just Fish) (Just "Nemo") Nothing


completePet :: Pet' Maybe -> Pet' Maybe
completePet (Pet x y t) = Pet x y t'
  where
    t' = Just $ Toy (Just "ball") (Just False)




labelPet :: Pet' Maybe -> Pet' (Annotate (Maybe Int) :. Maybe)
labelPet = hkdhoist pxyEmpty fxn . nestLabel
  where
    fxn :: (Annotate [Int] :. Maybe) z -> (Annotate (Maybe Int) :. Maybe) z
    fxn (O (Annotate ix's (Just x))) = O $ Annotate (Just (sum ix's)) (Just x)
    fxn (O (Annotate ix's Nothing))  = O $ Annotate Nothing Nothing





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
