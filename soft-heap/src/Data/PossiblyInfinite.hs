{-# LANGUAGE Safe #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}---Werror #-} as we are not implementing full Num instance

module Data.PossiblyInfinite(PossiblyInfinite(..)) where

data PossiblyInfinite a=Finite a | Infinite deriving(Show)
deriving instance (Eq a)=> Eq (PossiblyInfinite a)
deriving instance (Ord a)=> Ord (PossiblyInfinite a)
instance (Num a)=>Num (PossiblyInfinite a) where
    {-#SPECIALIZE instance Num (PossiblyInfinite Int)#-}
    (+) (Finite _) (Infinite)=Infinite
    (+) (Infinite) (Finite _)=Infinite
    (+) (Finite a) (Finite b)=Finite (a+b)
    (+) (Infinite) (Infinite)=Infinite
    (*) (Finite _) (Infinite)=Infinite
    (*) (Infinite) (Finite _)=Infinite
    (*) (Finite a) (Finite b)=Finite (a*b)
    (*) (Infinite) (Infinite)=Infinite
    fromInteger x=Finite (fromInteger x)
