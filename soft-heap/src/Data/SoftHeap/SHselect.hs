module Data.SoftHeap.SHselect (shSelect) where
import Data.SoftHeap
import Control.Monad.ST

--TODO finish
shSelect :: (Ord a)=>[a]-> Int -> a
shSelect l k
    | k==1 = minimum l
    | otherwise = runST $ do
        undefined
