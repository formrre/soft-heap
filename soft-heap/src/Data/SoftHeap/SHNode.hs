{-# LANGUAGE Safe #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExplicitForAll #-}

module Data.SoftHeap.SHNode(newSHItem,insert,makeHeapNode,meld,findMin,deleteMin,deleteItem,iKey,element,SHItem(),Node()) where
import Data.Natural
import Data.PossiblyInfinite
import Data.STRef
import Control.Monad.ST
import Data.Ord
import Data.Eq
import Data.Bool
import Control.Monad
import Data.Word
import Prelude((+),undefined,(.),Integral(..))

-- |type of items in the SoftHeap
data SHItem s k e where
    SHItem :: (Ord k) => STRef s Bool -> STRef s (SHItem s k e) -> PossiblyInfinite k -> e -> SHItem s k e
    NullSHItem :: (Ord k) => SHItem s k e

-- |creates new SHItem
--  important for arbitrary deletions
newSHItem :: forall k e s. (Ord k) => k -> e -> ST s (SHItem s k e)
newSHItem k e = mdo
    delRef <- newSTRef False
    itRef <- newSTRef (SHItem delRef itRef (Finite k) e)
    readSTRef itRef

element :: forall k e s. (Ord k) => SHItem s k e -> e
element (SHItem _ _ _ e)=e

-- |returns key of an SHItem
iKey :: forall k e s. (Ord k) => SHItem s k e -> PossiblyInfinite k
iKey (SHItem _ _ k _)=k
iKey NullSHItem = Infinite

-- |returns next SHItem on the item list
iNext :: forall k e s. (Ord k)=>SHItem s k e -> ST s (SHItem s k e)
iNext NullSHItem = return NullSHItem
iNext (SHItem _ ref _ _)=readSTRef ref

-- |returns the STRef in current heap referring to the next SHItem
iNextRef :: forall k e s. (Ord k) => SHItem s k e ->STRef s (SHItem s k e)
iNextRef NullSHItem =undefined
iNextRef (SHItem _ ref _ _)=ref

-- |sets the next Item of to the given Item
setINext :: forall k e s. (Ord k) => SHItem s k e -> SHItem s k e -> ST s ()
setINext (SHItem _ ref _ _) toSet = writeSTRef ref toSet
setINext NullSHItem _ = undefined

isDeleted :: forall k e s. (Ord k) => SHItem s k e -> ST s Bool
isDeleted (SHItem delRef _ _ _)=readSTRef delRef

setDeleted :: forall k e s. (Ord k) => SHItem s k e -> ST s ()
setDeleted (SHItem delRef _ _ _)=writeSTRef delRef True

data Node s k e where
    Node :: (Ord k) => STRef s (SHItem s k e) -> STRef s (PossiblyInfinite k) -> STRef s (PossiblyInfinite Word) -> STRef s (Node s k e) -> STRef s (Node s k e) -> STRef s (Node s k e) -> Node s k e
    NullNode :: (Ord k) => Node s k e

set :: forall k e s. (Ord k) => Node s k e ->ST s (SHItem s k e)
set NullNode = return NullSHItem
set (Node itSet _ _ _ _ _)=readSTRef itSet

key :: forall k e s. (Ord k) => Node s k e -> ST s (PossiblyInfinite k)
key NullNode = return Infinite
key (Node _ k _ _ _ _)=readSTRef k

rank :: forall k e s. (Ord k) => Node s k e -> ST s (PossiblyInfinite Word)
rank NullNode = return Infinite
rank (Node _ _ rk _ _ _)=readSTRef rk

left :: forall k e s. (Ord k) => Node s k e -> ST s (Node s k e)
left NullNode = return NullNode
left (Node _ _ _ l _ _)=readSTRef l

right :: forall k e s. (Ord k) => Node s k e -> ST s (Node s k e)
right NullNode = return NullNode
right (Node _ _ _ _ r _)=readSTRef r

next :: forall k e s. (Ord k) => Node s k e -> ST s (Node s k e)
next NullNode = return NullNode
next (Node _ _ _ _ _ n)=readSTRef n

nextRef :: forall k e s. (Ord k) => Node s k e -> STRef s (Node s k e)
nextRef NullNode = undefined
nextRef (Node _ _ _ _ _ n)=n

setSet :: forall k e s. (Ord k) => Node s k e -> SHItem s k e -> ST s ()
setSet (Node itSet _ _ _ _ _) toSet=writeSTRef itSet toSet
setSet NullNode _=undefined

setLeft :: forall k e s. (Ord k) => Node s k e -> Node s k e -> ST s ()
setLeft (Node _ _ _ l _ _) toSet=writeSTRef l toSet
setLeft NullNode _=undefined

setRight :: forall k e s. (Ord k) => Node s k e -> Node s k e -> ST s ()
setRight (Node _ _ _ _ r _) toSet=writeSTRef r toSet
setRight NullNode _=undefined

setNext :: forall k e s. (Ord k) => Node s k e -> Node s k e -> ST s ()
setNext (Node _ _ _ _ _ n) toSet=writeSTRef n toSet
setNext NullNode _=undefined

makeRoot :: forall k e s. (Ord k) => SHItem s k e -> ST s (Node s k e)
makeRoot NullSHItem=undefined
makeRoot it@(SHItem _ iN k _) = do
    writeSTRef iN it
    keyRefNode<-newSTRef k
    itRefNode<-newSTRef it
    rkRefNode<-newSTRef (Finite 0)
    leftRefNode<-newSTRef NullNode
    rightRefNode<-newSTRef NullNode
    nextRefNode<-newSTRef NullNode
    let newNode=Node itRefNode keyRefNode rkRefNode leftRefNode rightRefNode nextRefNode
    return newNode

-- |link creates a new Node which is then double even filled
link :: forall k e s. (Ord k) => PossiblyInfinite Word -> Node s k e -> Node s k e -> ST s (Node s k e)
link t x@NullNode y = do
    setRef<-newSTRef NullSHItem
    rkRef<-newSTRef Infinite
    leftRef<-newSTRef x
    rightRef<-newSTRef y
    keyRef<-newSTRef undefined
    nextRef'<-newSTRef undefined
    let z=Node setRef keyRef rkRef leftRef rightRef nextRef'
    defill t z
    return z
link t x@(Node _ _ rk _ _ _) y = do
    setRef<-newSTRef NullSHItem
    oldRk<-readSTRef rk
    rkRef<-newSTRef (oldRk+1)
    leftRef<-newSTRef x
    rightRef<-newSTRef y
    keyRef<-newSTRef undefined
    nextRef'<-newSTRef undefined
    let z=Node setRef keyRef rkRef leftRef rightRef nextRef'
    defill t z
    return z

-- |creates new root node
makeHeapNode :: forall k e s. (Ord k) => Node s k e
makeHeapNode=NullNode

-- |swaps the nodes on the root list to findable order and returns the new root
keySwap :: forall k e s. (Ord k) => Node s k e -> ST s (Node s k e)
keySwap h=do
    x<-next h
    hKey<-key h
    xKey<-key x
    if hKey <= xKey
        then return h
        else do
            xNext<-next x
            setNext h xNext
            setNext x h
            return x

-- |swaps the nodes on the root list to meldable order and returns the new root
rankSwap :: forall k e s. (Ord k) => Node s k e -> ST s (Node s k e)
rankSwap h=do
    x<-next h
    hRk<-rank h
    xRk<-rank x
    if hRk <= xRk
        then return h
        else do
            xNext<-next x
            setNext h xNext
            setNext x h
            return x

-- |returns the tuple (current minimum cost,item of such minimum current cost)
findMin :: forall k e s. (Ord k) => PossiblyInfinite Word -> STRef s (Node s k e) -> ST s (PossiblyInfinite k,SHItem s k e)
findMin t h = deleteMinCatchup t h >> (readSTRef h >>= (\hIn -> key hIn >>=(\k->(set hIn >>= iNext)>>=(return . ((,) k)))))

-- |predicate which checks if given Node is a NullNode
isNull :: forall k e s. Node s k e -> Bool
isNull NullNode = True
isNull _ = False

-- |fill a given Node once or twice; if we know the t
-- twice only if rank(node) is even and has at least one child to be filled in from after the first filling, and is above the level t
-- this is where the corruption comes from i.e. having multiple items in 1 node
-- analysis of this operation comes from the section 4. of the paper
defill :: (Ord k)=>PossiblyInfinite Word -> Node s k e -> ST s ()
defill _ NullNode=undefined
defill t x@(Node _ _ rk _ _ _)=do
    fill t x
    irk@(Finite r)<-readSTRef rk
    lf<-left x
    if(irk>t && (mod r 2)==0 && (isNull lf))then (fill t x) else return ()
    return ()

-- |auxilliary function to check if an Item is a NullItem
isNullSHItem :: forall k e s. (Ord k) => SHItem s k e -> Bool
isNullSHItem NullSHItem = True
isNullSHItem _ = False

-- |function which takes a boolean value and if the predicate is true returns the firstfirst monadic arguments
whenElse :: (Monad m)=>Bool -> m () -> m () -> m ()
whenElse p f s=if p then f else s

-- |same as whenElse but the Boolean value is instead taken from the context of the ST monad
whenElseST :: ST s Bool -> ST s () -> ST s () -> ST s ()
whenElseST p f s=do
    b<-p
    whenElse b f s

-- |check whether a certain action returns the NullNode
isNullST :: forall k e s. (Ord k) => ST s (Node s k e)->ST s Bool
isNullST s=do
    n<-s
    if(isNull n) then return True else return False

-- |crucial operation of the whole heap
-- fills the given Node, t is passed cause  the function can call defill
-- filling first fixes the order of children
-- then it catenates the item list of the left child to the node and procedes to defill the left child if it's not a leaf
fill :: forall k e s. (Ord k)=>PossiblyInfinite Word -> Node s k e -> ST s ()
fill _ NullNode=return ()
fill t x@(Node _ k _ l r _)=do
    lNode<-readSTRef l
    lKey<-key lNode
    rNode<-readSTRef r
    rKey<-key rNode
    if lKey>rKey then swap l r else return ()
    lN<-readSTRef l
    lK<-key lN
    writeSTRef k lK
    lSet<-set lN
    s<-set x
    whenElse (isNullSHItem s) (setSet x lSet) (elseSwap lSet s)
    lX<-left x
    setSet lX NullSHItem
    rX<-right x
    whenElseST (isNullST (ll x)) (setLeft x rX >> setRight x NullNode) (defill t lX)
    return ()
    where
        elseSwap lSet s=do
            iSetNext<-iNext lSet
            sNext<-iNext s
            setINext lSet sNext
            setINext s iSetNext
        ll w=do
            y<-left w
            z<-left y
            return z

-- |helper function to swap 2 references
swap :: STRef s a -> STRef s a -> ST s ()
swap x y=do
    vx<-readSTRef x
    vy<-readSTRef y
    writeSTRef x vy
    writeSTRef y vx

-- |meldableInsert checks if rank of the node x is smaller then the one of the first root; if yes we make x the new root
--  if not we link the first root and the new node together
--  and recurse by inserting the new node to the next root until the first 2 roots obey the rank order
meldableInsert :: forall k e s. (Ord k) => PossiblyInfinite Word -> Node s k e->Node s k e->ST s (Node s k e)
meldableInsert t x h=do
    rkX<-rank x
    rkH<-rank h
    if rkX < rkH 
        then keySwap h >>=setNext x >> return x
        else link t x h >>=(\l -> (next h>>=rankSwap)>>=(meldableInsert t l))

-- |meldableMeld orders its inputs by rank i.e. h1 is of smaller rank
--  and procedes with melding (by means of meldableMeld) the next root into h2
--  then it meldableInserts the h1 to the resulting root list
--  h1 becomes unusable
meldableMeld :: forall k e s. (Ord k) => PossiblyInfinite Word -> STRef s (Node s k e) -> STRef s (Node s k e)->ST s (Node s k e)
meldableMeld t h1 h2=do
    h1In<-readSTRef h1
    h2In<-readSTRef h2
    rk1<-rank h1In
    rk2<-rank h2In
    if rk1>rk2
        then swap h1 h2
        else return ()
    if isNull h2In
        then return h1In
        else next h1In >>= rankSwap >>= writeSTRef h1 >> meldableMeld t h1 h2 >>= meldableInsert t h1In

-- |meld meldableMelds the 2 heaps in the meldable order and then switches into findable order
--  makes its 2 arguments unusable
meld :: forall k e s. (Ord k) =>PossiblyInfinite Word -> STRef s (Node s k e) -> STRef s (Node s k e) -> ST s (Node s k e)
meld t h1 h2=do
    h1In<-readSTRef h1
    h2In<-readSTRef h2
    rsh1<-rankSwap h1In
    rsh2<-rankSwap h2In
    writeSTRef h1 rsh1
    writeSTRef h2 rsh2
    meldableMeld t h1 h2 >>= keySwap

-- |insert is a meldableInsert in the meldableOrder and then switch to the findable order
insert :: forall k e s. (Ord k) => PossiblyInfinite Word -> SHItem s k e -> Node s k e -> ST s (Node s k e)
insert t e h= makeRoot e >>= (\n->rankSwap h>>=meldableInsert t n) >>= keySwap

reorder :: forall k e s. (Ord k) => PossiblyInfinite Word -> STRef s (Node s k e) -> ST s (Node s k e)
reorder k h=do
    hIn<-readSTRef h
    n<-next hIn
    rk<-rank n
    if rk<k
        then rankSwap hIn >>= writeSTRef h
            >> readSTRef h >>= (\han ->reorder k (nextRef han) >>= setNext han)
        else return ()
    keySwap hIn

--note Eq on STRef does sameMutVar#; which does MO_EQ which gets translated to .cmm pointer equality
deleteMin_ :: forall k e s. (Ord k) => PossiblyInfinite Word -> STRef s (Node s k e) -> ST s (Node s k e)
deleteMin_ t h=do
    hIn<-readSTRef h
    setH<-set hIn
    let e=iNextRef setH
    eIn<-readSTRef e
    if e/= (iNextRef eIn) 
        then (iNext eIn >>=setINext setH) >> return hIn
        else setSet hIn NullSHItem >> rank hIn >>= (\k -> (whenElseST (isNullST (left hIn)) (next hIn>>=writeSTRef h) (defill t hIn)) >> reorder k h)

-- |keeps calling deleteMin_ on the heap until the minimum item is not marked as already deleted; used by both findMin and deleteMin; modifies the h passed to it
deleteMinCatchup :: forall k e s. (Ord k) => PossiblyInfinite Word -> STRef s (Node s k e) -> ST s ()
deleteMinCatchup t h=do
    hIn<-readSTRef h
    setH<-set hIn
    let e=iNextRef setH
    eIn<-readSTRef e
    d<-isDeleted eIn
    if d then ((deleteMin_ t h) >>= (writeSTRef h)) >> deleteMinCatchup t h  else return ()

-- |catchup on abritrary deletions using deleteMinCatchup and then deleteMin_ once more
deleteMin :: forall k e s. (Ord k) => PossiblyInfinite Word -> STRef s (Node s k e) -> ST s (Node s k e)
deleteMin t h = deleteMinCatchup t h >> deleteMin_ t h

-- |deletes an arbitrary item
deleteItem :: forall k e s. (Ord k) => SHItem s k e -> ST s ()
deleteItem NullSHItem=undefined
deleteItem x=setDeleted x
