import SoftHeap
import Control.Monad.ST
import Data.STRef
shtest :: PossiblyInfinite Int
shtest=runST $ do
    let e=makeHeapNode :: Node s Int
    c<-newItem (4::Int)
    root<-insert Infinite c e
    (k,_)<-findMin root
    return k

main=do
        let (Finite x)=shtest
        putStrLn $ show x
