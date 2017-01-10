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
type TiState    = (TiStack, TiDump, TiHeap, TiGlobal, TiStats)

-- | collect addresses of nodes to be reduced
type TiStack    = [Addr]

getStackDepth :: TiState -> Int
getStackDepth (stack, _, _, _, _) = length stack

-- | dump is a stack of stack
type TiDump     = [TiStack]

getDumpDepth :: TiState -> Int
getDumpDepth (_, dump, _, _, _) = length dump

-- | store all supercombinators (in the beginning) and every expression
-- node (gradually added during evaluation, more specifically, in the 
-- process of instantiation)
type TiHeap     = Heap (Node Name)

-- | a list providing effective query(/O(log n)) from supercombinator
-- to address
type TiGlobal   = Assocs Name Addr

-- | tiStats will collect run-time statistics, for now it accumulates
-- total step taken, reductions(split to spercombinator reductions and
-- primitive reductions) and max stack depth
data TiStats = TiStep { steps :: Int,
                        prRds :: Int,
                        scRds :: Int,
                        maxStk :: Int,
                        maxDmp :: Int }

-- | initial stats
tiStatsInit :: TiStats
tiStatsInit = TiStep 0 0 0 0 0

-- | increase step counter by one
tiStatsIncStep :: TiStats -> TiStats
tiStatsIncStep (TiStep n x y z w) = TiStep (n+1) x y z w

-- | increase primitive reduction counter by one
tiStatsIncPR :: TiStats -> TiStats
tiStatsIncPR (TiStep x n y z w) = TiStep x (n+1) y z w

-- | increase supercombinator counter by one
tiStatsIncSR :: TiStats -> TiStats
tiStatsIncSR (TiStep x y n z w) = TiStep x y (n+1) z w

-- | change the value of stored value of max stack depth
tiStatsChangeMaxStk :: Int -> TiStats -> TiStats
tiStatsChangeMaxStk n' (TiStep x y z n w) = TiStep x y z n' w

-- | change the value of stored value of max dump depth
tiStatsChangeMaxDmp :: Int -> TiStats -> TiStats
tiStatsChangeMaxDmp n' (TiStep x y z w n) = TiStep x y z w n'

-- | apply a function to stats in a state to make a new state
applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (s, d, h, g, ss) = (s, d, h, g, f ss)

-- | nodes stored in the heap
data Node a = NAp Addr Addr
            | NSC Name [a] (Expr a)
            | NNum Int
            | NInd Addr
            | NPrim Name Primitive
                 -- ^ the @Name@ field is just for debugging

-- | the primitive operations, served for pattern matching in
-- primitive instantiation
data Primitive = Neg | Add | Sub | Mul | Div 
    deriving Enum

prDefs :: [(Name, Primitive)]
prDefs = zip ["negate", "+", "-", "*", "/"] [(Neg)..]

-- | @run@ the program, takes source code and gives its output. It is a 
-- composition of parser, compiler, evaluator and showing-the-result.
run :: String -> String
run = showResult . eval . compile . parse

-- | transform @CoreProgram@ data structure into initial state
compile :: CoreProgram -> TiState
compile cp = ([mainAddr], initDump, initHeap, globals, tiStatsInit)
    where initDump = []
          (initHeap, globals) = buildInitialHeap scDefs
          mainAddr = aLookup globals "main" (error "main is not defined")
          scDefs = cp ++ preludeDefs

-- | use supercombinators to build initial heap, and assign their name to 
-- addresses in the heap in globals
buildInitialHeap :: [CoreScDef] -> (TiHeap, TiGlobal)
buildInitialHeap scDefs = (heap2, globals)
    where globals = aFromList $ globalsTmp1 ++ globalsTmp2
          (heap1, globalsTmp1) = mapAccuml allocateSc hInitial scDefs
          (heap2, globalsTmp2) = mapAccuml allocatePr heap1 prDefs
          allocateSc h (name, args, body) = let 
            (hn, addr) = hAlloc h (NSC name args body) in (hn, (name, addr))
          allocatePr h (name, prim) = let
            (hn, addr) = hAlloc h (NPrim name prim) in (hn, (name, addr))

-----------------------------------------------------------------------------

-- | generate a sequence of state from inital to final
eval :: TiState -> [TiState]
eval state = state : followingStates
    where followingStates
            | tiFinalState state = []
            | otherwise = eval . doAdmin . advanceState $ state

-- | do the administration work between steps
doAdmin :: TiState -> TiState
doAdmin state@(_, _, _, _, stats) = applyToStats (tiStatsIncStep.f.g) state
        where f | csd < sd = id | otherwise = tiStatsChangeMaxStk csd
              g | cdd < dd = id | otherwise = tiStatsChangeMaxDmp cdd
              csd = getStackDepth state
              sd = maxStk stats
              cdd = getDumpDepth state
              dd = maxDmp stats

-- | determine if reduction accomplished
tiFinalState :: TiState -> Bool
tiFinalState (stack, dump, heap, _, _) = 
    case stack of   [soleAddr] -> null dump &&
                        (isDataNode $ hLookup heap soleAddr)
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
        NAp a1 a2 -> apStep a1 a2 state
        NSC name args body -> applyToStats tiStatsIncSR $
            scStep name args body state
            -- applying a supercombinator is more complicate, 
            --  a specialized function will deal with it
        NNum _ -> numStep state
        NInd aInd -> (aInd:stack, dump, heap, globals, stat)
        NPrim name primitive -> applyToStats tiStatsIncPR $
            prStep name primitive state
            -- applying a primitive also needs an auxiliary function

-- | a function advancing one step when the head of stack points to 
-- a function application node, it will check the operand in case it being
-- a indirection node
apStep :: Addr -> Addr -> TiState -> TiState
apStep a1 a2 (stack, dump, heap, globals, stats) = 
    (a1:stack, dump, newHeap, globals, stats)
        where newHeap = case hLookup heap a2 of 
                NInd addr -> hUpdate heap (head stack) (NAp a1 addr)
                node -> heap

-- | a function advancing one step when the head of stack points to
-- a supercombinator
scStep :: Name -> [Name] -> CoreExpr -> TiState -> TiState
scStep sc args body (stack, dump, heap, globals, stat) =
    (iScAddr:newStack, dump, newHeap, globals, stat)
        where (newStack, argList) = getArgs sc args (tail stack) heap
              iScAddr = stack !! length args
              newHeap = instantiateAndUpdate 
                body iScAddr heap (argList `aCombine` globals)
                
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

-- | instantiate an expression and use it to update given the node
instantiateAndUpdate :: CoreExpr -> Addr -> TiHeap -> TiGlobal -> TiHeap
instantiateAndUpdate expr addr heap varList = case expr of
    ENum num -> hUpdate heap addr (NNum num)
    EVar var -> hUpdate heap addr (NInd $ aLookup varList var 
        (error $ "can't find defination of variable "++var))
    EAp f x -> hUpdate heap2 addr $ NAp addr1 addr2
        where (heap1, addr1) = instantiate f heap varList
              (heap2, addr2) = instantiate x heap1 varList
    EConstr tag arity -> undefined
    ELet flag defs body -> 
        instantiateAndUpdateLet flag defs body addr heap varList
    ELam vars body -> undefined

-- | instantiate let binding
instantiateLet ::   IsRec -> [(Name, CoreExpr)] -> CoreExpr 
               ->   TiHeap -> TiGlobal -> (TiHeap, Addr)
instantiateLet isRec defs body heap varList = instantiate body newHeap env
        where env = localEnv `aCombine` varList
              (newHeap, localEnv) = instantiateDefs isRec defs heap varList

-- | instantiate let binding and update the heap with it
instantiateAndUpdateLet :: IsRec -> [(Name, CoreExpr)] -> CoreExpr
                        -> Addr -> TiHeap -> TiGlobal -> TiHeap
instantiateAndUpdateLet isRec defs body addr heap varList = 
    instantiateAndUpdate body addr newHeap env
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

-- | check the dump to determine throwing error or recovering stack
numStep :: TiState -> TiState
numStep ([addr], dump, heap, globals, stats) = 
    case dump of
      [] -> error "number can not apply to anything."
      [unaryOp,ap]:dump -> ([unaryOp, ap], dump, newHeap, globals, stats)
        where newHeap = hUpdate heap ap (NAp unaryOp addr)
      [binOp,ap1,ap2]:dump -> ([binOp,ap1,ap2], dump, newHeap, globals, stats)
        where newHeap = hUpdate heap ap1 (NAp binOp addr)

-- | a function advancing one step when the head of stack points to 
-- a primitive operation
prStep :: Name -> Primitive -> TiState -> TiState
prStep name primitive state = case primitive of 
    Neg -> primUnary negate state
    Add -> primArith name (+) state
    Sub -> primArith name (-) state
    Mul -> primArith name (*) state
    Div -> primArith name div state

primUnary :: (Int -> Int) -> TiState -> TiState
primUnary func (prim:[ap], dump, heap, globals, stats) = 
    case hLookup heap operand of
      NNum num -> 
          ([ap], dump, hUpdate heap ap (NNum (func num)), globals, stats)
      node -> ([operand], [prim,ap]:dump, heap, globals, stats)
    where NAp _ operand = hLookup heap ap

primArith :: Name -> (Int -> Int -> Int) -> TiState -> TiState
primArith name func (prim:[ap1,ap2], dump, heap, globals, stats) = 
    case hLookup heap operand of
      NNum num -> primUnary (func num) 
        ([ap1,ap2], dump, heap, globals, stats)
      node -> ([operand], [prim,ap1,ap2]:dump, heap, globals, stats)
    where NAp _ operand = hLookup heap ap1

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
      NInd addr -> cStr "NInd" `cAppend` cLPNum 4 addr
      NPrim prim _ -> cStr "NPrim " `cAppend` cStr prim
    ]

pprStatsInState :: TiState -> Cseq
pprStatsInState (_, _, heap, _, stats) = cConcat 
    [   cStr "This program takes ", cNum $ steps stats, 
        cStr " steps, including", cNewline, cStr $ space 4, 
        cIndent reductions, cNewline, 
        cStr "There are ", cIndent heapOps, cNewline, 
        cStr "Max stack depth is ", cNum $ maxStk stats, cNewline, 
        cStr "Max dump depth is ", cNum $ maxDmp stats ]
        where reductions = cConcat 
                [   cNum $ scRds stats, 
                    cStr " supercombinator reductions;", cNewline, 
                    cNum $ prRds stats, cStr " primitive reductions." ]
              heapOps = cConcat 
                [   cNum $ hGetAllocTimes heap, cStr " heap allocations", 
                    cNewline, cNum $ hGetUpdateTimes heap, 
                    cStr " heap updates", cNewline, 
                    cNum $ hGetFreeTimes heap, cStr " heap free operations" ]
                

