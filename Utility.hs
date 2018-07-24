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

module Utility (
    
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
    , aDomain, aRange, aLookup, aToList
    
    -- * A.5 Other useful function definitions
    , mapAccuml, sort, space

    )where

-- | The heap is represented as a quadruple, containing
--
--  * the unused address pool
--  * the used addresses
--  * a complete binary search tree 
--  * an extra part count heap maniputations
--
--  every node in the BST in indexed by an address taken out of 
--  the address pool. The following functions are all from A.1.1 in appendix,
--  but implementation differently, and @showaddr@ is not needed 
--  since @Addr@ is a type synonym of @Int@.
type Heap a = ([Addr], [Addr], BST Addr a, (Int, Int, Int))

-- | address are represented as numbers
type Addr = Int

-- | an initialised empty heap
hInitial :: Heap a
hInitial = ([1..], [], emptyBST, (0, 0, 0))

-- | allocate an object in heap and return the address and new heap
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc ([], _, _, _)  _ = error "empty address pool"
hAlloc (addr:ap, uap, tree, (al, ud, fr)) node = 
    ((ap, addr:uap, insertInBST addr node tree, (al+1, ud, fr)), addr)

-- | update an object at specific address
hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (ap, uap, tree, (al, ud, fr)) addr node = 
    (ap, uap, updateBST addr node tree, (al, ud+1, fr))

-- | remove a specific object, for now it only changes address pool
hFree :: Heap a -> Addr -> Heap a
hFree heap@(ap, uap, tree, (al, ud ,fr)) addr
    | 2 * (al - fr) < sizeOfBST tree = hFree (cleanHeap heap) addr
    | otherwise = (addr:ap, del addr uap, tree, (al, ud, fr+1))
    where   del x0 (x:xs)
                | x0 == x = xs
                | otherwise = del x0 xs
            del _ [] = error "deleting non-existing node"

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

-- cleans the heap, removing all node not belonging used address pool
cleanHeap :: Heap a -> Heap a
cleanHeap (ap, uap, tree, stas@(al, _, fr)) = (ap, uap, newTree, stas)    
    where   newTree = foldl (flip deleteInBST) tree (take n ap)
            n = sizeOfBST tree - al + fr

-- | use Map in Data.Map to implement @Assocs@
type Assocs a b = BST a b

-- | @aLookup aList key default@ find the value of @key@ in @aList@
-- and return @default@ if the key is not in associate list
aLookup :: Ord k => Assocs k v -> k -> v -> v
aLookup al key def = findWithDefaultInBST def key al

-- | gives all the keys of the associate list
aDomain :: Ord k => Assocs k v -> [k]
aDomain = map fst . convertListFromBST

-- | gives all the values of the associate list
aRange :: Ord k => Assocs k v -> [v]
aRange = map snd . convertListFromBST

-- | an empty associate list
aEmpty :: Assocs k v
aEmpty = emptyBST

-- | Union two associate lists. When key crashes, the value from
-- first assocs list is prefered.
aCombine :: Ord k => Assocs k v -> Assocs k v -> Assocs k v
aCombine = combineBST

-- | insert a pair of key-value in to assoc list
aInsert :: Ord k => (k,v) -> Assocs k v -> Assocs k v
aInsert (k, v) = insertInBST k v

-- | convert a list of key-value pair into assocs list
aFromList :: Ord k => [(k,v)] -> Assocs k v
aFromList = convertListToBST

-- | convert an assocs list into a list of key-value pair
aToList :: Ord k => Assocs k v -> [(k, v)]
aToList = convertListFromBST

-----------------------------------------------------------------------

-- | a binary tree with a number in each node telling the size of itself
data BST k a    = Tip
                | BinNode Int k a (BST k a) (BST k a)
    deriving Show

-- the critical weight for performing balance operation
weight :: Int
weight = 4

emptyBST :: BST k a 
emptyBST = Tip

-- build a tree from key, value and subtrees and make sure 
-- the size is correct
buildBST :: Ord k => k -> a -> BST k a -> BST k a -> BST k a
buildBST key obj lt rt = 
    let size = 1 + sizeOfBST lt + sizeOfBST rt 
    in BinNode size key obj lt rt

-- insert new element in BST, since it's used in a heap with 
-- an address pool, the key is promised to be distinguished with
-- every node in BST 
insertInBST :: Ord k => k -> a -> BST k a -> BST k a
insertInBST key obj Tip = BinNode 1 key obj Tip Tip
insertInBST key obj (BinNode _ rtkey rtobj lt rt) = balanceBST newTree
    where   newTree = case compare key rtkey of
                LT -> buildBST rtkey rtobj (insertInBST key obj lt) rt
                GT -> buildBST rtkey rtobj lt (insertInBST key obj rt)
                EQ -> buildBST key obj lt rt

-- balance a tree after inserting/deleting one element,
-- use size as balance criterion
balanceBST :: Ord k => BST k a -> BST k a
balanceBST Tip = Tip
balanceBST tree@(BinNode _ _ _ lt rt)
        | lsize + rsize < 2 = tree
        | lsize >= weight * rsize =
            let BinNode _ _ _ llt lrt = lt
                llsize = sizeOfBST llt
                lrsize = sizeOfBST lrt
            in case compare llsize lrsize of
                LT -> doubleRotationR tree
                _ -> singleRotationR tree
        | lsize * weight <= rsize =
            let BinNode _ _ _ rlt rrt= rt
                rlsize = sizeOfBST rlt
                rrsize = sizeOfBST rrt 
            in case compare rlsize rrsize of
                GT -> doubleRotationL tree
                _ -> singleRotationL tree
        | otherwise = tree
        where   lsize = sizeOfBST lt
                rsize = sizeOfBST rt

-- rotation functions
singleRotationL, singleRotationR, doubleRotationL, doubleRotationR :: 
            Ord k => BST k a -> BST k a
singleRotationL Tip = Tip
singleRotationL (BinNode rtsize rtkey rtobj lt rt) =
    let BinNode _ rkey robj rlt rrt = rt 
        newlt = buildBST rtkey rtobj lt rlt
    in  BinNode rtsize rkey robj newlt rrt

singleRotationR Tip = Tip
singleRotationR (BinNode rtsize rtkey rtobj lt rt) = 
    let BinNode _ lkey lobj llt lrt = lt
        newrt = buildBST rtkey rtobj lrt rt
    in BinNode rtsize lkey lobj llt newrt

doubleRotationL Tip = Tip
doubleRotationL (BinNode rtsize rtkey rtobj sub1t rt) = 
    let BinNode _ rkey robj rlt sub4t = rt
        BinNode _ rlkey rlobj sub2t sub3t = rlt
        newlt = buildBST rtkey rtobj sub1t sub2t
        newrt = buildBST rkey robj sub3t sub4t
    in BinNode rtsize rlkey rlobj newlt newrt

doubleRotationR Tip = Tip
doubleRotationR (BinNode rtsize rtkey rtobj lt sub4t) = 
    let BinNode _ lkey lobj sub1t lrt = lt
        BinNode _ lrkey lrobj sub2t sub3t = lrt
        newlt = buildBST lkey lobj sub1t sub2t
        newrt = buildBST rtkey rtobj sub3t sub4t
    in BinNode rtsize lrkey lrobj newlt newrt

-- update an element in BST, and for the same reason in @insertInBST@,
-- no need to check key existed in the origin BST
updateBST :: Ord k => k -> a -> BST k a -> BST k a
updateBST _ _ Tip = error "updating a non-existing node"
updateBST key obj (BinNode size k o lc rc) = 
    case compare key k of
      LT -> BinNode size k o (updateBST key obj lc) rc
      GT -> BinNode size k o lc (updateBST key obj rc)
      EQ -> BinNode size k obj lc rc

deleteInBST :: Ord k => k -> BST k a -> BST k a
deleteInBST _ Tip = Tip
deleteInBST key (BinNode _ rtkey rtobj lt rt) = balanceBST newTree
    where newTree = case compare key rtkey of
            LT -> buildBST rtkey rtobj (deleteInBST key lt) rt
            GT -> buildBST rtkey rtobj lt (deleteInBST key rt)
            EQ -> combineBST lt rt

-- when key crushes, keep the node from the first tree
combineBST :: Ord k => BST k a -> BST k a -> BST k a
combineBST tree1 tree2 = convertListToBST $ 
    merge (convertListFromBST tree1) (convertListFromBST tree2)
    where   merge [] x = x
            merge y [] = y
            merge ms@((km, vm):mt) ns@((kn, vn):nt)
                | km > kn = (kn, vn) : merge ms nt
                | otherwise = (km, vm) : merge mt ns

convertListFromBST :: Ord k => BST k a -> [(k, a)]
convertListFromBST Tip = []
convertListFromBST (BinNode _ key obj lt rt) = 
    convertListFromBST lt ++ (key, obj) : convertListFromBST rt

convertListToBST :: Ord k => [(k, a)] -> BST k a
convertListToBST = foldl (flip $ uncurry insertInBST) emptyBST 

findInBST :: Ord k => k -> BST k a -> a
findInBST = findWithDefaultInBST (error "key not found")

findWithDefaultInBST :: Ord k => a -> k -> BST k a -> a
findWithDefaultInBST def _ Tip = def
findWithDefaultInBST def key (BinNode _ k o lt rt) = 
    case compare key k of
        LT -> findWithDefaultInBST def key lt
        GT -> findWithDefaultInBST def key rt
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
mapAccuml _ acc [] = (acc,[])
mapAccuml f acc (b:bs) = (acc'', c:cs)
    where (acc', c) = f acc b
          (acc'', cs) = mapAccuml f acc' bs

-- | sort a list with ascending order
sort :: Ord a => [a] -> [a]
sort [] = []
sort [a] = [a]
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
