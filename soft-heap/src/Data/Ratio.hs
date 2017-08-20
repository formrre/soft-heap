module Data.Ratio(Ratio(..)) where

newtype Ratio a=Ratio (a,a)

instance (Integral a)=>Num (Ratio a) where
	(+) (Ratio (a,b)) (Ratio (c,d))=Ratio (numerator,denominator)
		where
			newNumerator=a*d+b*c
			newDenominator=b*d
			gcdNumDen=gcd newNumerator newDenominator
			numerator=newNumerator `div` gcdNumDen
			denominator=newDenominator `div` gcdNumDen
	(*) (Ratio (a,b)) (Ratio (c,d))=Ratio (numerator,denominator)
		where
			newNumerator=a*c
			newDenominator=b*d
			gcdNumDen=gcd newNumerator newDenominator
			numerator=newNumerator `div` gcdNumDen
			denominator=newDenominator `div` gcdNumDen
instance (Integral a)=>Fractional (Ratio a) where
	(/) (Ratio (a,b)) (Ratio (c,d))=Ratio (numerator,denominator)
		where
			newNumerator=a*d
			newDenominator=b*c
			gcdNumDen=gcd newNumerator newDenominator
			numerator=newNumerator `div` gcdNumDen
			denominator=newDenominator `div` gcdNumDen
