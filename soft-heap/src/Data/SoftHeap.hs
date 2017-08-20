{-# LANGUAGE Safe #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
--{-# LANGUAGE NoImplicitPrelude #-}

module Data.SoftHeap(findMin,insert,makeHeap,deleteMin,newSHItem,meld,SHItem(),key,element,SoftHeap(),PossiblyInfinite(..),SNat(..),Natural(..),SHItem',SoftHeap',insert',findMin',meld',deleteMin') where

import qualified Data.SoftHeap.SHNode as N
import Data.SoftHeap.SHNode hiding(insert,meld,findMin,deleteMin)
import Data.STRef
import Data.PossiblyInfinite
import Data.Natural
import Control.Monad.ST
import Control.Exception.Base(assert)
import Data.Bits
import Data.Word

data TrueT
data FalseT

-- | rename iKey key
key :: forall k e s. (Ord k) => SHItem s k e -> PossiblyInfinite k
key = iKey 

-- |TF for type-level equality 
type family TypeEq a b where
    TypeEq a a = TrueT
    TypeEq a b = FalseT

--add num < denom!!!!

-- |main-type of SoftHeap
data SoftHeap s k e (epsilonNum :: Natural) (epsilonDenom :: PossiblyInfinite Natural) where 
    SoftHeap :: (Ord k,TypeEq epsilonDenom (Finite Zero) ~ FalseT)=> PossiblyInfinite Word -> STRef s (Node s k e) -> SoftHeap s k e epsilonNum epsilonDenom

-- |Singleton type of naturals 
data SNat (n::Natural) where
    SZero :: SNat Zero
    SSucc :: SNat n -> SNat (Succ n)

-- |Singleton type of possibly infinite naturals
data SNatInf (n::PossiblyInfinite Natural) where
    SNatInfNat :: SNat k -> SNatInf (Finite k)
    SNatInfInf :: SNatInf Infinite

-- |converts singleton natural to Word, takes O(n) where n is the natural
toWord :: SNat n -> Word
toWord SZero=0
toWord (SSucc n)=1+(toWord n)

-- |constructs a heap with corruption rate m/n, where m is a natural and n is a possibly infinite natural
makeHeap :: forall k e s m n. (Ord k,TypeEq n (Finite Zero) ~ FalseT) => SNat m -> SNatInf n -> ST s (SoftHeap s k e m n)
makeHeap m (SNatInfNat n)=do
    ref<-makeHeap' undefined
    let numer=toWord m
    let denom=toWord n
    return (SoftHeap (t numer denom) ref)
    where
        --make 2nd case unrepresentable 
        t numero denomo
                | denomo==0 = undefined
                | numero>=denomo = undefined
                | numero==0 = Infinite
                | otherwise = Finite $ tActual numero denomo -- ceil(log2(3denomo/numero)) for 0<numero<denomo
makeHeap m SNatInfInf=do
    ref<-makeHeap' undefined
    return (SoftHeap Infinite ref)

tActual :: Word -> Word -> Word
tActual numero denomo
    | isPower2 (3*denomo) numero = logBase2Floor ((3*denomo) `div` numero)
    | otherwise = 1+(logBase2Floor ((3*denomo) `div` numero))

isPower2Whole :: Word -> Bool
isPower2Whole x
    | popCount x == 0 = True
    | popCount x == 1 = True
    | otherwise = False

isPower2 :: Word -> Word -> Bool
isPower2 numerator denominator
    | numerator `rem` denominator /= 0 = False
    | isPower2Whole (numerator `div` denominator) = True
    | otherwise = False

logBase2Floor :: Word -> Word
logBase2Floor x = fromIntegral $ finiteBitSize x - 1 -countLeadingZeros x

makeHeap' _=newSTRef makeHeapNode

-- |inserts a new element with key into the heap and returns the newly created item for use with arbitrary deletions
insert :: forall k e s m n. (Ord k)=>SoftHeap s k e m n->k->e->ST s (SHItem s k e)
insert (SoftHeap t nRef) k e=do
    it<-newSHItem k e
    n<-readSTRef nRef
    newN<-N.insert t it n
    writeSTRef nRef newN
    return it

-- |returns the tuple (current minimum cost,item of the current minimum cost)
findMin :: forall k e s m n. (Ord k)=>SoftHeap s k e m n->ST s (PossiblyInfinite k,SHItem s k e)
findMin (SoftHeap _ nRef)=do
    node<-readSTRef nRef
    N.findMin node

--this melds 2 Soft Heaps; this is highly unsafe tough
meldIn :: forall k e s m n. (Ord k)=>SoftHeap s k e m n->SoftHeap s k e m n->ST s (SoftHeap s k e m n)
meldIn (SoftHeap t0 n0) (SoftHeap t1 n1)=assert (t0==t1) $ do
    newRoot<-N.meld t0 n0 n1
    rootRef<-newSTRef newRoot
    return (SoftHeap t0 rootRef)

-- |evaluates it's third argument with second argument as a parameter and melds the result into first
meld :: forall k e s m n a. (Ord k)=>SoftHeap s k e m n->a->(a->SoftHeap s k e m n)->ST s ()
meld h1@(SoftHeap _ n) param bracketH=do
    (SoftHeap _ nodeRef)<-meldIn h1 $ bracketH param
    nodeRefIn<-readSTRef nodeRef
    writeSTRef n nodeRefIn
    return ()

-- |deletes the minimum Item out of a heap
deleteMin :: forall k e s m n. (Ord k)=>SoftHeap s k e m n->ST s ()
deleteMin (SoftHeap t n)=do
    newRoot<-N.deleteMin t n
    writeSTRef n newRoot
    return ()


-- |alias for SoftHeap with keys only
type SoftHeap' s k (m::Natural) (n::PossiblyInfinite Natural)=SoftHeap s k () m n

-- |alias for SHItem with keys only
type SHItem' s k=SHItem s k ()

-- |insertion with keys only
insert' :: forall k s t m n. (Ord k)=>SoftHeap' s k m n->k->ST s (SHItem' s k)
insert' h k=insert h k ()

-- |find minimum with keys only
findMin' :: forall k s t m n. (Ord k)=>SoftHeap' s k m n->ST s (PossiblyInfinite k,SHItem' s k)
findMin' h=findMin h

-- |meld with keys only
meld' :: forall k s t a m n. (Ord k)=>SoftHeap' s k m n->a->(a->SoftHeap' s k m n)->ST s ()
meld' h1 param bracketH=meld h1 param bracketH

-- |delete minimum with keys only
deleteMin' :: forall k s t m n. (Ord k)=>SoftHeap' s k m n->ST s ()
deleteMin' h=deleteMin h
