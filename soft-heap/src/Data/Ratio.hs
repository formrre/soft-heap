module Data.Ratio(Ratio(..)) where

newtype Ratio a=Ratio (a,a)

instance Num (Ratio a) where
	(+) (Ratio (a,b)) (Ratio (c,d))=Ratio (undefined,undefined)
