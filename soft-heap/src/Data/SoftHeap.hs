{-# LANGUAGE Safe #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExplicitForAll #-}
module Data.SoftHeap(findMin,insert,makeHeap,deleteMin,newSHItem,meld,SHItem(),SoftHeap(),PossiblyInfinite(..),SNat(..),Natural(..)) where
import qualified Data.SoftHeap.SHNode as N
import Data.SoftHeap.SHNode hiding(insert,meld,findMin,deleteMin)
import Data.STRef
import Data.PossiblyInfinite
import Data.Natural
import Control.Monad.ST
import Control.Exception.Base(assert)
data SoftHeap s k e (t::Natural) where 
    SoftHeap :: (Ord k)=>PossiblyInfinite Natural -> STRef s (Node s k e) -> SoftHeap s k e t

data SNat (n::Natural) where
    SZero :: SNat Zero
    SSucc :: SNat n -> SNat (Succ n)
toNat :: SNat n -> Natural
toNat SZero=Zero
toNat (SSucc n)=Succ (toNat n)
makeHeap :: forall k e s t. (Ord k) => SNat t-> ST s (SoftHeap s k e t)
makeHeap t=do
    ref<-makeHeap' undefined
    let val=toNat t
    return (SoftHeap (Finite val) ref)
makeHeap' :: (Ord k)=>k -> ST s (STRef s (Node s k e))
makeHeap' _=newSTRef makeHeapNode

insert :: forall k e s t. (Ord k)=>SoftHeap s k e t->k->e->ST s ()
insert (SoftHeap t nRef) k e=do
    it<-newSHItem k e
    n<-readSTRef nRef
    newN<-N.insert t it n
    writeSTRef nRef newN
    return ()

findMin :: forall k e s t. (Ord k)=>SoftHeap s k e t->ST s (PossiblyInfinite k,SHItem s k e)
findMin (SoftHeap _ nRef)=do
    node<-readSTRef nRef
    N.findMin node

--this melds 2 Soft Heaps; this is highly unsafe tough
meld' :: forall k e s t. (Ord k)=>SoftHeap s k e t->SoftHeap s k e t->ST s (SoftHeap s k e t)
meld' (SoftHeap t0 n0) (SoftHeap t1 n1)=assert (t0==t1) $ do
    newRoot<-N.meld t0 n0 n1
    rootRef<-newSTRef newRoot
    return (SoftHeap t0 rootRef)

--executes bracketH with param and melds it into first heap
meld :: forall k e s t a. (Ord k)=>SoftHeap s k e t->a->(a->SoftHeap s k e t)->ST s ()
meld h1@(SoftHeap _ n) param bracketH=do
    (SoftHeap _ nodeRef)<-meld' h1 $ bracketH param
    nodeRefIn<-readSTRef nodeRef
    writeSTRef n nodeRefIn
    return ()

deleteMin :: forall k e s t. (Ord k)=>SoftHeap s k e t->ST s ()
deleteMin (SoftHeap t n)=do
    newRoot<-N.deleteMin t n
    writeSTRef n newRoot
    return ()
