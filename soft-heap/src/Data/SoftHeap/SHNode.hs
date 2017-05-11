{-# LANGUAGE Safe #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExplicitForAll #-}
module Data.SoftHeap.SHNode(newSHItem,insert,makeHeapNode,meld,findMin,deleteMin,iKey,SHItem(),Node()) where
import Data.Natural
import Data.PossiblyInfinite
import Data.STRef
import Control.Monad.ST
import Data.Ord
import Data.Eq
import Data.Bool
import Control.Monad
import Prelude((+),undefined,(.))

data SHItem s k e where
    SHItem :: (Ord k) => STRef s (SHItem s k e) -> PossiblyInfinite k -> e -> SHItem s k e
    NullSHItem :: (Ord k) => SHItem s k e

newSHItem :: forall k e s. (Ord k) => k -> e -> ST s (SHItem s k e)
newSHItem k e = mdo
    itRef <- newSTRef (SHItem itRef (Finite k) e)
    readSTRef itRef

iKey :: forall k e s. (Ord k) => SHItem s k e -> PossiblyInfinite k
iKey (SHItem _ k _)=k
iKey NullSHItem = Infinite

iNext :: forall k e s. (Ord k)=>SHItem s k e -> ST s (SHItem s k e)
iNext NullSHItem = return NullSHItem
iNext (SHItem ref _ _)=readSTRef ref

iNextRef :: forall k e s. (Ord k) => SHItem s k e ->STRef s (SHItem s k e)
iNextRef NullSHItem =undefined
iNextRef (SHItem ref _ _)=ref

setINext :: forall k e s. (Ord k) => SHItem s k e -> SHItem s k e -> ST s ()
setINext (SHItem ref _ _) toSet = writeSTRef ref toSet
setINext NullSHItem _ = undefined

-- make rank a Word and make Natural alias for Word for the sake of efficiency
data Node s k e where
    Node :: (Ord k) => STRef s (SHItem s k e) -> STRef s (PossiblyInfinite k) -> STRef s (PossiblyInfinite Natural) -> STRef s (Node s k e) -> STRef s (Node s k e) -> STRef s (Node s k e) -> Node s k e
    NullNode :: (Ord k) => Node s k e

set :: forall k e s. (Ord k) => Node s k e ->ST s (SHItem s k e)
set NullNode = return NullSHItem
set (Node itSet _ _ _ _ _)=readSTRef itSet

key :: forall k e s. (Ord k) => Node s k e -> ST s (PossiblyInfinite k)
key NullNode = return Infinite
key (Node _ k _ _ _ _)=readSTRef k

rank :: forall k e s. (Ord k) => Node s k e -> ST s (PossiblyInfinite Natural)
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
makeRoot it@(SHItem iN k _) = do
    writeSTRef iN it
    keyRefNode<-newSTRef k
    itRefNode<-newSTRef it
    rkRefNode<-newSTRef (Finite Zero)
    leftRefNode<-newSTRef NullNode
    rightRefNode<-newSTRef NullNode
    nextRefNode<-newSTRef NullNode
    let newNode=Node itRefNode keyRefNode rkRefNode leftRefNode rightRefNode nextRefNode
    return newNode

link :: forall k e s. (Ord k) => PossiblyInfinite Natural->Node s k e -> Node s k e -> ST s (Node s k e)
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

makeHeapNode :: forall k e s. (Ord k) => Node s k e
makeHeapNode=NullNode

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

findMin :: forall k e s. (Ord k) => Node s k e -> ST s (PossiblyInfinite k,SHItem s k e)
findMin h = key h >>=(\k->(set h >>= iNext)>>=(return . ((,) k)))

isNull :: forall k e s. Node s k e -> Bool
isNull NullNode = True
isNull _ = False

--when defilling NullNode as in python float("INF")%2==nan which has strange comparison use these
defill :: (Ord k)=>PossiblyInfinite Natural -> Node s k e -> ST s ()
defill _ NullNode=undefined
defill t x@(Node _ _ rk _ _ _)=do
    fill t x
    irk@(Finite r)<-readSTRef rk
    lf<-left x
    if(irk>t && (modNat r 2)==0 && (isNull lf))then (fill t x) else return ()
    return ()

isNullSHItem :: forall k e s. (Ord k) => SHItem s k e -> Bool
isNullSHItem NullSHItem = True
isNullSHItem _ = False

whenElse :: (Monad m)=>Bool -> m () -> m () -> m ()
whenElse p f s=if p then f else s

whenElseST :: ST s Bool -> ST s () -> ST s () -> ST s ()
whenElseST p f s=do
    b<-p
    whenElse b f s

isNullST :: forall k e s. (Ord k) => ST s (Node s k e)->ST s Bool
isNullST s=do
    n<-s
    if(isNull n) then return True else return False

fill :: forall k e s. (Ord k)=>PossiblyInfinite Natural -> Node s k e -> ST s ()
fill _ NullNode=return () --just in case
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

swap :: STRef s a -> STRef s a -> ST s ()
swap x y=do
    vx<-readSTRef x
    vy<-readSTRef y
    writeSTRef x vy
    writeSTRef y vx

meldableInsert :: forall k e s. (Ord k) =>PossiblyInfinite Natural -> Node s k e->Node s k e->ST s (Node s k e)
meldableInsert t x h=do
    rkX<-rank x
    rkH<-rank h
    if rkX < rkH 
        then keySwap h >>=setNext x >> return x
        else link t x h >>=(\l -> (next h>>=rankSwap)>>=(meldableInsert t l))

--eliminate rewrapping please!!!!
meldableMeld :: forall k e s. (Ord k) =>PossiblyInfinite Natural -> STRef s (Node s k e) ->STRef s (Node s k e)->ST s (Node s k e)
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
            else (next h1In >>= rankSwap) >>= newSTRef >>= (\res-> meldableMeld t res h2) >>= meldableInsert t h1In

--makes its 2 arguments unusable
meld :: forall k e s. (Ord k) =>PossiblyInfinite Natural -> STRef s (Node s k e) -> STRef s (Node s k e) -> ST s (Node s k e)
meld t h1 h2=do
    h1In<-readSTRef h1
    h2In<-readSTRef h2
    rsh1<-rankSwap h1In
    rsh2<-rankSwap h2In
    writeSTRef h1 rsh1
    writeSTRef h2 rsh2
    meldableMeld t h1 h2 >>= keySwap

insert :: forall k e s. (Ord k) => PossiblyInfinite Natural -> SHItem s k e -> Node s k e -> ST s (Node s k e)
insert t e h= makeRoot e >>= (\n->rankSwap h>>=meldableInsert t n) >>= keySwap

reorder :: forall k e s. (Ord k) => PossiblyInfinite Natural -> STRef s (Node s k e) -> ST s (Node s k e)
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
--eliminate rewrapping
deleteMin :: forall k e s. (Ord k) => PossiblyInfinite Natural -> STRef s (Node s k e) -> ST s (Node s k e)
deleteMin t h=do
    hIn<-readSTRef h
    setH<-set hIn
    let e=iNextRef setH
    eIn<-readSTRef e
    if e/= (iNextRef eIn) 
        then (iNext eIn >>=setINext setH) >> return hIn
        else setSet hIn NullSHItem >> rank hIn >>= (\k -> (whenElseST (isNullST (left hIn)) (next hIn>>=writeSTRef h) (defill t hIn)) >> reorder k h)
