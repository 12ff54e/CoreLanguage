-----------------------------------------------------------------------------
-- |
-- Module   : CoreLanguage.Utility
--
-- Heap implemented using Binary Search Tree(BST), the interface is defined
-- same as in the book. The function that remove object in heap is 
-- ill-implement because I have not yet found out how to maintain balance of 
-- the tree after deleting nodes in it.
--
-- Associate list defined as type synonym of /Map/ in /Data.Map/, use
-- function in the same module to create the interface.
--
-- Besides, some useful function (those in A.5) also defined.
--
-----------------------------------------------------------------------------

module CoreLanguage.Utility (
    
    -- * A.1 Heap
    
    -- ** Heap types
    Heap(..), Addr

    -- ** Heap Construction
    , hInitial, hAlloc, hUpdate, hFree
    
    -- ** Heap Query
    , hLookup, hAddresses, hSize

    -- ** Extract statistics
    , hGetAllocTimes, hGetUpdateTimes, hGetFreeTimes

    -- ** tbd
    , hNull, hIsnull
    
    -- * A.2 The association list

    -- ** Associate list type
    , Assocs(..)
    
    -- ** Associate list Construction
    , aCombine, aInsert, aEmpty, aFromList

    -- ** Associate list Query
    , aDomain, aRange, aLookup
    
    -- * A.5 Other useful function definitions
    , mapAccuml, sort, space

    )where

import Data.Bits (shiftL)
import Data.Map (Map, keys, elems, findWithDefault, 
                    insert, empty, union, fromList)

-- | The heap is represented as a quadruple, containing
--
--  * the unused address pool
--  * the used addresses
--  * a complete binary search tree 
--  * an extra part count heap maniputations
--
--  every node in the BST in indexed by an address taken out of 
--  the address pool, since the node index are monotonic when insertBSTed
--  in the BST, the tree is also balanced. The following functions are
--  all from A.1.1 in appendix, but implementation differently, and 
--  @showaddr@ is not needed since @Addr@ is a type synonym of @Int@.
type Heap a = ([Addr], [Addr], BST Addr a, (Int, Int, Int))

-- | address are represented as numbers
type Addr = Int

-- | an initialised empty heap
hInitial :: Heap a
hInitial = ([1..], [], emptyBST, (0, 0, 0))

-- | allocate an object in heap and return the address and new heap
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (addr:ap, uap, tree, (al, ud, fr)) node = 
    ((ap, addr:uap, insertBST addr node tree, (al+1, ud, fr)), addr)

-- | update an object at specific address
hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (ap, uap, tree, (al, ud, fr)) addr node = 
    (ap, uap, updateBST addr node tree, (al, ud+1, fr))

-- | remove a specific object, for now it only changes address pool
hFree :: Heap a -> Addr -> Heap a
hFree (ap, uap, tree, (al, ud ,fr)) addr = 
    (addr:ap, del addr uap, tree, (al, ud, fr+1))
        where del x0 (x:xs)
                | x0 == x = xs
                | otherwise = del x0 xs

-- | look for an object in the heap
hLookup :: Heap a -> Addr -> a
hLookup (_, _, tree, _) addr = findInBST addr tree

-- | return addresses of all objects in the heap
hAddresses :: Heap a -> [Addr]
hAddresses (_, uap, _, _) = uap

-- | return the number of objects in the heap
hSize :: Heap a -> Int
hSize (_, _, tree, _) = sizeOfBST tree

-- | get the number of allocation had been applied to this heap
hGetAllocTimes :: Heap a -> Int
hGetAllocTimes (_, _, _, (n, _, _)) = n

-- | get the number of updates had been applied to this heap
hGetUpdateTimes :: Heap a -> Int
hGetUpdateTimes (_, _, _, (_, n, _)) = n 

-- | get the number of free operation had been applied to this heap
hGetFreeTimes :: Heap a -> Int
hGetFreeTimes (_, _, _, (_, _, n)) = n 

-- | @hNull@ is an address guaranteed to differ from every address 
-- returned by @hAlloc@
hNull :: Addr
hNull = 0

-- | @hIsnull@ tells whether an address is this distinguished value
hIsnull :: Addr -> Bool
hIsnull a = a == hNull

-- | use Map in Data.Map to implement @Assocs@
type Assocs a b = Map a b

-- | @aLookup aList key default@ find the value of @key@ in @aList@
-- and return @default@ if the key is not in associate list
aLookup :: Ord k => Assocs k v -> k -> v -> v
aLookup al key def = findWithDefault def key al

-- | gives all the keys of the associate list
aDomain :: Assocs k v -> [k]
aDomain = keys

-- | gives all the values of the associate list
aRange :: Assocs k v -> [v]
aRange = elems

-- | an empty associate list
aEmpty :: Assocs k v
aEmpty = empty

-- | Union two associate lists. When key crashes, the value from
-- first assocs list is prefered.
aCombine :: Ord k => Assocs k v -> Assocs k v -> Assocs k v
aCombine = union

-- | insert a pair of key-value in to assoc list
aInsert :: Ord k => (k,v) -> Assocs k v -> Assocs k v
aInsert (k,v) al = insert k v al

-- | convert a list of key-value pair into assocs list
aFromList :: Ord k => [(k,v)] -> Assocs k v
aFromList = fromList

-----------------------------------------------------------------------

-- | a binary tree with a number in each node telling the size of itself
data BST k a    = Tip
                | BinNode Int k a (BST k a) (BST k a)
    deriving Show

emptyBST :: BST k a 
emptyBST = Tip

-- insert new element in BST, since it's used in a heap with 
-- an address pool, the key is promised to be distinguished with
-- every node in BST 
insertBST :: Ord k => k -> a -> BST k a -> BST k a
insertBST key obj Tip = BinNode 1 key obj Tip Tip
insertBST key obj tree@(BinNode size k o lc rc)
    | size' `elemInfAsc` powerOf2 = case compare key k of
                LT -> BinNode size' key obj Tip tree
                GT -> BinNode size' key obj tree Tip
    | otherwise = case compare key k of
                    LT -> BinNode size' k o (insertBST key obj lc) rc
                    GT -> BinNode size' k o lc (insertBST key obj rc)
                    EQ -> BinNode size' k obj lc rc
        where elemInfAsc t (a:as)
                | t==a = True
                | t<a = False
                | otherwise = t `elemInfAsc` as
              powerOf2 = iterate (flip shiftL 1) 1
              size' = size+1

-- update an element in BST, and for the same reason in @insertBST@,
-- no need to check key existed in the origin BST
updateBST :: Ord k => k -> a -> BST k a -> BST k a
updateBST key obj (BinNode size k o lc rc) = 
    case compare key k of
      LT -> BinNode size k o (updateBST key obj lc) rc
      GT -> BinNode size k o lc (updateBST key obj rc)
      EQ -> BinNode size k obj lc rc

findInBST :: Ord k => k -> BST k a -> a
findInBST _ Tip = error "the key did not in the BST"
findInBST key (BinNode size k o lc rc) = 
    case compare key k of 
      LT -> findInBST key lc
      GT -> findInBST key rc
      EQ -> o

sizeOfBST :: BST k a -> Int
sizeOfBST Tip = 0
sizeOfBST (BinNode size _ _ _ _) = size

-----------------------------------------------------------------------

-- | a combination of map and foldl
mapAccuml   :: (a -> b -> (a,c))    -- ^ function take the old accumulator and
                                    -- element from input list, generates new 
                                    -- accumulator and result list element
            -> a                    -- ^ initial accumulator
            -> [b]                  -- ^ input list
            -> (a, [c])             -- ^ final acc and result list
mapAccuml f acc [] = (acc,[])
mapAccuml f acc (b:bs) = (acc'', c:cs)
    where (acc', c) = f acc b
          (acc'', cs) = mapAccuml f acc' bs

-- | sort a list with ascending order
sort :: Ord a => [a] -> [a]
sort [] = []
sort (a:[]) = [a]
sort as = merge (sort xs) (sort ys)
    where (xs,ys) = splitAt (length as `div`2) as
          merge ms [] = ms
          merge [] ns = ns
          merge ms@(m:mt) ns@(n:nt)
            | m<n = m : merge mt ns
            | otherwise = n : merge ms nt

-- | generate a string of @n@ spaces
space :: Int -> String
space n = replicate n ' '
