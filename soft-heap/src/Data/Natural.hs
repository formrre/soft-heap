{-# LANGUAGE DataKinds #-}
module Data.Natural(Natural(..),modNat,zero,one,two) where

data Natural=Zero | Succ Natural deriving(Ord,Eq)
zero :: Natural
zero=Zero

one :: Natural
one=Succ Zero
two :: Natural
two=Succ one

instance Num Natural where
        (+) x Zero=x
        (+) x (Succ y)=(+) (Succ x) y
        (-) x Zero=x
        (-) (Succ x) (Succ y)=(-) x y

--inefficient
--TODO make Word64 backed runtime representation
modNat :: Natural -> Natural -> Natural
modNat _ Zero=undefined
modNat x y
        | x<y = x
        | otherwise = modNat (x-y) y
