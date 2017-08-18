{-# LANGUAGE DataKinds #-}
module Data.SoftHeap.SHselect(shSelect) where
import Data.SoftHeap
import Control.Monad.ST
import Data.Natural

sOne=SSucc SZero
sTwo=SSucc sOne
sThree=SSucc sTwo


--returns 
partition :: (Ord k) => [k] -> k -> Int
partition l x = undefined

slice :: Int -> Int -> [k] -> [k]
slice from to xs = take (to - from + 1) (drop from xs)

--TODO finish
shSelect :: (Ord k) => [k] -> Int -> k
shSelect l k
    | k==1 = minimum l
    | otherwise = runST $ do
        h<-heapify sThree l
        let third=(length l) `div` 3
        x<-shSelectLoop h third
        let xIndex=partition l x
        if k < xIndex then return $ shSelect (slice 0 (xIndex-1) l) k else return $ shSelect (slice xIndex (k-xIndex+1) l) k

shSelectLoop :: (Ord k) => SoftHeap' s k t -> Int -> ST s k
shSelectLoop h 0=do
    x<-findMin h
    deleteMin h
    let (Finite ret)=fst x
    return ret
shSelectLoop h times=do
    deleteMin' h
    shSelectLoop h (times-1)

heapify' :: (Ord k) => [k] -> SoftHeap' s k t -> ST s ()
heapify' [] h=return ()
heapify' (x:xs) h=insert' h x>>heapify' xs h


heapify :: (Ord k) => SNat t -> [k] -> ST s (SoftHeap' s k (Finite t))
heapify t l=makeHeap t>>=(\h->heapify' l h>>return h)
