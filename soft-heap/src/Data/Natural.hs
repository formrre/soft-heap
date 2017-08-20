{-# LANGUAGE DataKinds #-}
module Data.Natural(Natural(..),zero,one,two) where

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
