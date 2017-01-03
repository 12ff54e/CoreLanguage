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

getStackDepth :: TiState -> Int
getStackDepth (stack, _, _, _, _) = length stack

data TiDump      = DummyType

-- | store all supercombinators (in the beginning) and every expression
-- node (gradually added during evaluation, more specifically, in the 
-- process of instantiation)
type TiHeap      = Heap (Node Name)

-- | a list providing effective query(/O(log n)) from supercombinator
-- to address
type TiGlobal    = Assocs Name Addr

-- | tiStats will collect run-time statistics, for now its just number
-- of steps taken
data TiStats = TiStep { steps :: Int,
                        prRds :: Int,
                        scRds :: Int,
                        maxStk :: Int }

-- | initial stats
tiStatsInit :: TiStats
tiStatsInit = TiStep 0 0 0 0

-- | increase step counter by one
tiStatsIncStep :: TiStats -> TiStats
tiStatsIncStep (TiStep n x y z) = TiStep (n+1) x y z

-- | increase primitive reduction counter by one
tiStatsIncPR :: TiStats -> TiStats
tiStatsIncPR (TiStep x n y z) = TiStep x (n+1) y z

-- | increase supercombinator counter by one
tiStatsIncSR :: TiStats -> TiStats
tiStatsIncSR (TiStep x y n z) = TiStep x y (n+1) z

-- | change the value of stored value of max stack depth
tiStatsChangeMaxStk :: Int -> TiStats -> TiStats
tiStatsChangeMaxStk n' (TiStep x y z n) = TiStep x y z n'

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
doAdmin state@(_, _, _, _, stats) = applyToStats (tiStatsIncStep . f) state
        where f | csd < sd = id | otherwise = tiStatsChangeMaxStk csd
              csd = getStackDepth state
              sd = maxStk stats

-- | determine if reduction accomplished
tiFinalState :: TiState -> Bool
tiFinalState (stack, _, heap, _, _) = 
    case stack of   [soleAddr] -> isDataNode $ hLookup heap soleAddr
                    [] -> error "empty stack!"
                    stack -> False

-- | is this node a data node?
isDataNode :: Node a -> Bool
isDataNode (NNum _) = True
isDataNode node = False

-- | advance one step of the state
advanceState :: TiState -> TiState
advanceState state@(addr:stack, dump, heap, globals, stat) =
    case hLookup heap addr of
        NAp a1 a2 -> (a1:addr:stack, dump, heap, globals, stat)
        NSC name args body -> applyToStats tiStatsIncSR $
            scStep name args body state
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
                
-- | take all arguments needed for instantiation from the stack, the name
-- of supercombinator are also needed for comprehensive error message
getArgs :: Name -> [Name] -> TiStack -> TiHeap -> (TiStack, TiGlobal)
getArgs _ [] stack _ = (stack, aEmpty)
getArgs sc _ [] _ = error $ sc++" is applied to too few arguments"
getArgs sc (name:args) (addr:stack) heap = (newStack, argList') 
    where argList' = aInsert (name, operand) argList
          NAp _ operand = hLookup heap addr
          (newStack, argList) = getArgs sc args stack heap

-- | instantiate an expression, tranvers it to substitude all local and 
-- global bindings (packed in @varList@ argument) and put all nodes in heap
instantiate :: CoreExpr -> TiHeap -> TiGlobal -> (TiHeap, Addr)
instantiate expr heap varList = case expr of 
    ENum num -> hAlloc heap (NNum num)
    EVar var -> (heap, aLookup varList var 
        (error $ "can't find defination of variable "++var))
    EAp f x -> hAlloc heap2 $ NAp addr1 addr2
        where (heap1, addr1) = instantiate f heap varList
              (heap2, addr2) = instantiate x heap1 varList
    EConstr tag arity -> error "Can't instantiate data constructor yet."
    ELet flag defs body -> instantiateLet flag defs body heap varList
    ELam vars body -> error "Can't instantiate lambda expression yet."

-- | instantiate let binding
instantiateLet ::   IsRec -> [(Name, CoreExpr)] -> CoreExpr 
               ->   TiHeap -> TiGlobal -> (TiHeap, Addr)
instantiateLet isRec defs body heap varList = instantiate body newHeap env
        where env = localEnv `aCombine` varList
              (newHeap, localEnv) = instantiateDefs isRec defs heap varList

-- | instantiate a list of variable bindings, put their body in heap and 
-- attach their name-address list to the enviroment
instantiateDefs ::  IsRec -> [(Name, CoreExpr)] -> TiHeap -> TiGlobal
                ->  (TiHeap, TiGlobal)
instantiateDefs isRec defs heap varList = (newHeap, env)
    where (newHeap, localDefs) = mapAccuml allocDef heap defs
          env = aFromList localDefs `aCombine` varList
          allocDef h (name, expr) = (hn, (name, addr))
            where (hn, addr)
                    | nonRecursive = instantiate expr h varList
                    | recursive = instantiate expr h (env `aCombine` varList)

------------------------------------------------------------------------------

-- | Extract informations and format them for printing, exploiting string
-- container defined in Base module
showResult :: [TiState] -> String
showResult states = cToStr $ 
    cNumList (map pprState states) `cAppend` pprStatsInState (last states)

pprState :: TiState -> Cseq
pprState (stack, _, heap, _, _) = 
    cIntercalate cNewline $ pprNode <$> stack <*> pure heap
    
pprNode :: Addr -> TiHeap -> Cseq  
pprNode addr heap = cConcat [ cLPNum 3 addr, cStr ": ", 
    case hLookup heap addr of 
      NAp a1 a2 -> cConcat [ cStr "NAp", cLPNum 4 a1, cLPNum 4 a2 ]
      NSC sc _ _ -> cStr "NSC " `cAppend` cStr sc
      NNum num -> cStr "NNum " `cAppend` cNum num
    ]

pprStatsInState :: TiState -> Cseq
pprStatsInState (_, _, heap, _, stats) = 
    cConcat [   cStr "This program takes ", cNum $ steps stats, 
                cStr " steps, ", cNum $ scRds stats,
                cStr " supercombinator reductions, and ",
                cNum . prRds $ stats, cStr " primitive reductions.",
                cNewline, cStr "There are ", cNum $ hGetAllocTimes heap,
                cStr ", ", cNum $ hGetUpdateTimes heap, cStr ", ",
                cNum $ hGetFreeTimes heap, cStr " times of heap ",
                cStr "allocation, update and free operations.",
                cNewline, cStr "Max stack depth is ", cNum $ maxStk stats ]

