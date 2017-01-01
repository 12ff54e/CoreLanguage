------------------------------------------------------------------------------
-- | 
-- Module   : CoreLanguage.TemplateInstantiation
--
-- A simple graph reducer based on template instantiation. It uses a
-- state transition system to do the reduction.
--
------------------------------------------------------------------------------

module CoreLanguage.TemplateInstantiation (
    -- * RUN the code!
    run
    -- * debugging stuffs
    -- ** compilation process
    -- ** evaluation precess
    -- ** result formatting process
    ) where

import CoreLanguage.Base
import CoreLanguage.Parser
import CoreLanguage.Utility

-- a bunch of type definations prepared for the state transition system

-- | The state is a quadruple(in theory), here a extra element for run-time
-- performance statistics collection is added.
type TiState     = (TiStack, TiDump, TiHeap, TiGlobal, TiStats)

-- | collect addresses of nodes to be reduced
type TiStack     = [Addr]

data TiDump      = DummyType

-- | store all supercombinators (in the beginning) and every expression
-- node (gradually added during evaluation, more specifically, in the 
-- process of instantiation)
type TiHeap      = Heap (Node Name)

-- | a list providing effective query(/O(log n)) from supercombinator to address
type TiGlobal    = Assocs Name Addr

-- | tiStats will collect run-time statistics, for now its just number
-- of steps taken
data TiStats = TiStep Int

-- | initial stats
tiStatsInit :: TiStats
tiStatsInit = TiStep 0

-- | advance one step in tiStats
tiStatsIncStep :: TiStats -> TiStats
tiStatsIncStep (TiStep n) = TiStep (n+1)

-- | get current steps from tiStats
tiStatsGetStep :: TiStats -> Int
tiStatsGetStep (TiStep n) = n

-- | apply a function to stats in a state to make a new state
applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (s, d, h, g, ss) = (s, d, h, g, f ss)

-- | nodes stored in the heap
data Node a = NAp Addr Addr
            | NSC Name [a] (Expr a)
            | NNum Int
    deriving Show

-- | @run@ the program, takes source code and gives its output. It is a 
-- composition of parser, compiler, evaluator and showing-the-result.
run :: String -> String
run = showResult . eval . compile . parse

-- | transform @CoreProgram@ data structure into initial state
compile :: CoreProgram -> TiState
compile cp = ([mainAddr], initDump, initHeap, globals, tiStatsInit)
    where initDump = undefined
          (initHeap, globals) = buildInitialHeap scDefs
          mainAddr = aLookup globals "main" (error "main is not defined")
          scDefs = cp ++ preludeDefs

-- | use supercombinators to build initial heap, and assign their name to 
-- addresses in the heap in globals
buildInitialHeap :: [CoreScDef] -> (TiHeap, TiGlobal)
buildInitialHeap scDefs = (heap, globals)
    where globals = aFromList globalsTmp
          (heap, globalsTmp) = mapAccuml allocateSc hInitial scDefs
          allocateSc h (name, args, body) = (hn, (name, addr))
              where (hn, addr) = hAlloc h (NSC name args body)

-----------------------------------------------------------------------------

-- | generate a sequence of state from inital to final
eval :: TiState -> [TiState]
eval state = state : followingStates
    where followingStates
            | tiFinalState state = []
            | otherwise = eval . doAdmin . advanceState $ state

-- | do the administration work between steps
doAdmin :: TiState -> TiState
doAdmin = applyToStats tiStatsIncStep

-- | determine if reduction accomplished
tiFinalState :: TiState -> Bool
tiFinalState (stack, _, heap, _, _) = 
    case stack of   [soleAddr] -> isDataNode $ hLookup heap soleAddr
                    [] -> error "empty stack!"
                    stack -> False

-- | is this node a pure data node?
isDataNode :: Node a -> Bool
isDataNode (NNum _) = True
isDataNode node = False

-- | advance one step of the state
advanceState :: TiState -> TiState
advanceState state@(addr:stack, dump, heap, globals, stat) =
    case hLookup heap addr of
        NAp a1 a2 -> (a1:addr:stack, dump, heap, globals, stat)
        NSC name args body -> scStep name args body state 
            -- applying a supercombinator is more complicate, 
            --  a specialized function will dealing with it
        NNum _ -> error "number can not apply to anything"

-- | a function advancing one step when the head of stack points to
-- a supercombinator
scStep :: Name -> [Name] -> CoreExpr -> TiState -> TiState
scStep sc args body (addr:stack, dump, heap, globals, stat) =
    (iScAddr:newStack, dump, newHeap, globals, stat)
        where (newStack, argList) = getArgs sc args stack heap
              (newHeap, iScAddr) = 
                  instantiate body heap (aCombine argList globals)
                
-- | instantiate a supercombinator, tranvers its body expression and put all
-- nodes in heap
instantiate :: CoreExpr -> TiHeap -> TiGlobal -> (TiHeap, Addr)
instantiate expr heap varList = case expr of 
    ENum num -> hAlloc heap (NNum num)
    EVar var -> (heap, aLookup varList var 
        (error $ "can't find defination of variable "++var))
    EAp f x -> hAlloc heap2 $ NAp addr1 addr2
        where (heap1, addr1) = instantiate f heap varList
              (heap2, addr2) = instantiate x heap1 varList

-- | take all arguments needed for instantiation from the stack, the name
-- of supercombinator are also needed for comprehensive error message
getArgs :: Name -> [Name] -> TiStack -> TiHeap -> (TiStack, TiGlobal)
getArgs _ [] stack _ = (stack, aEmpty)
getArgs sc _ [] _ = error $ sc++" is applied to too few arguments"
getArgs sc (name:args) (addr:stack) heap = (newStack, argList') 
    where argList' = aInsert (name, operand) argList
          NAp _ operand = hLookup heap addr
          (newStack, argList) = getArgs sc args stack heap

-----------------------------------------------------------------------------

showResult :: [TiState] -> String
showResult = show . takeResult . last
    where takeResult ([addr], _, heap, _, stat) = num
            where NNum num = hLookup heap addr


