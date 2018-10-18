{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- {-# LANGUAGE OverlappingInstances #-}


module Main where
import           GHC.Generics
import           Data.Functor.Identity
import Data.HKD
import Data.Text
import Data.Typeable

main :: IO ()
main = putStrLn "hello HKD"




data Person' f = Person
  { name :: HKD f Text
  , address :: Address' f
  , pets :: HKD f [Pet' f]
  } deriving (Generic)

deriving instance Show (Person' Identity)
deriving instance Show (Person' Maybe)

data Pet' f = Pet
  { species :: f Species
  , petName :: f Text
  } deriving (Generic)

deriving instance Show (Pet' Identity)
deriving instance Show (Pet' Maybe)

data Species = Dog | Cat | Fish deriving (Generic, Eq, Show)

data Address' f = Address
  { street :: f Text
  , zipcode :: f Text
  , state :: f Text
  } deriving Generic

deriving instance Show (Address' Identity)
deriving instance Show (Address' Maybe)


person :: Person' Maybe
person = Person (Just "Jason") addr1 (Just [pet1, pet2])
addr1 = Address (Just "11732 Perry Street") (Just "80031") (Just "CO")
pet1 = Pet (Just Dog) (Just "Loki")
pet2 = Pet (Just Fish) (Just "Nemo")

hasChar :: Char -> Person' Maybe -> [String]
hasChar c = gnfold (Proxy :: Proxy Show) fxn
  where
    fxn :: Show a => Maybe a -> [String]
    fxn (Just x) = if c `elem` show x then [show x] else []
    fxn Nothing = []

                     

