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
type TiHeap     = Heap Node

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
                        maxDmp :: Int,
                        output :: [Int] }

-- | initial stats
tiStatsInit :: TiStats
tiStatsInit = TiStep 0 0 0 0 0 []

-- | increase step counter by one
tiStatsIncStep :: TiStats -> TiStats
tiStatsIncStep (TiStep n x y z w v) = TiStep (n+1) x y z w v

-- | increase primitive reduction counter by one
tiStatsIncPR :: TiStats -> TiStats
tiStatsIncPR (TiStep x n y z w v) = TiStep x (n+1) y z w v

-- | increase supercombinator counter by one
tiStatsIncSR :: TiStats -> TiStats
tiStatsIncSR (TiStep x y n z w v) = TiStep x y (n+1) z w v

-- | change the value of stored value of max stack depth
tiStatsChangeMaxStk :: Int -> TiStats -> TiStats
tiStatsChangeMaxStk n' (TiStep x y z n w v) = TiStep x y z n' w v

-- | change the value of stored value of max dump depth
tiStatsChangeMaxDmp :: Int -> TiStats -> TiStats
tiStatsChangeMaxDmp n' (TiStep x y z w n v) = TiStep x y z w n' v

tiStatsOutput :: ([Int] -> [Int]) -> TiStats -> TiStats
tiStatsOutput f (TiStep x y z w v o) = TiStep x y z w v (f o)

-- | apply a function to stats in a state to make a new state
applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (s, d, h, g, ss) = (s, d, h, g, f ss)

-- | nodes stored in the heap
data Node   = NAp Addr Addr             -- ^ function application
            | NSC Name [Name] CoreExpr  -- ^ supercombinator
            | NNum Int                  -- ^ number
            | NInd Addr                 -- ^ indirection
            | NConstr Int Int           -- ^ data constructor
            | NPrim Name Primitive
                -- ^ primitive, the @Name@ field is just for debugging
            | NData Int [Addr]
                -- ^ structured data type: tag and list of components

-- | the primitive operations, served for pattern matching in
-- primitive instantiation
data Primitive  = Neg | Add | Sub | Mul | Div 
                | Lt | Eq | Gt | Leq | Neq | Geq
                | CaseBool | CasePair | CaseList
                | Abort | Print
        deriving Enum

prDefs :: [(Name, Primitive)]
prDefs = zip (arith ++ compares ++ misc) [Neg ..]
    where arith = ["negate", "+", "-", "*", "/"]
          compares = ["<", "==", ">", "<=", "/=", ">="]
          misc = ["if", "casePair", "caseList", "abort", "print"]

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
          scDefs = cp ++ preludeDefs ++ extraPreludeDefs

-- | extra prelude definations, including basic logic functions
extraPreludeDefs :: CoreProgram
extraPreludeDefs = booleanDefs ++ pairDefs ++ listBasicDefs ++ listExtraDefs

booleanDefs :: CoreProgram
booleanDefs = 
    [   ("True", [], EConstr 1 0),
        ("False", [], EConstr 2 0),
        ("and", ["x", "y"], 
            EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "y")) 
                (EVar "False")),
        ("or", ["x", "y"],
            EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "True")) 
                (EVar "y")),
        ("not", ["x"],
            EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "False")) 
                (EVar "True")),
        ("xor", ["x", "y"],
            EAp (EAp (EAp (EVar "if") (EVar "x")) 
                     (EAp (EVar "not") (EVar "y"))) 
                (EVar "y")) ]

pairDefs :: CoreProgram
pairDefs = 
    [   ("Pair", [], EConstr 1 2),
        ("fst", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "k1")),
        ("snd", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "k2")) ]

listBasicDefs ::CoreProgram
listBasicDefs = 
    [   ("Nil", [], EConstr 1 0),
        ("Cons", [], EConstr 2 2),
        ("length", ["as"],
            EAp (EAp (EAp (EVar "caseList") (EVar "as")) (ENum 0)) 
            (EVar "prLength")),
        ("prLength", ["a","as"],
            EAp (EAp (EVar "+") (ENum 1)) 
                (EAp (EVar "length") (EVar "as"))),
        ("head", ["as"],
            EAp (EAp (EAp (EVar "caseList") (EVar "as")) (EVar "abort")) 
            (EVar "prHead")),
        ("tail", ["as"],
            EAp (EAp (EAp (EVar "caseList") (EVar "as")) (EVar "abort")) 
            (EVar "prTail")),
        ("prHead", ["a","as"],EVar "a"),
        ("prTail", ["a","as"],EVar "as") ]

listExtraDefs :: CoreProgram
listExtraDefs =
    [   ("zipWith", ["f", "as", "bs"],
            EAp (EAp (EAp (EVar "caseList") (EVar "as")) (EVar "Nil")) 
                (EAp (EAp (EVar "prTmpZipWith") (EVar "f")) (EVar "bs"))),
        ("prTmpZipWith", ["f", "bs", "a", "as"],
            EAp (EAp (EAp (EVar "caseList") (EVar "bs")) (EVar "Nil")) 
                (EAp (EAp (EAp (EVar "prZipWith") (EVar "f")) (EVar "a")) 
                     (EVar "as"))),
        ("prZipWith", ["f", "a", "as", "b", "bs"],
            EAp (EAp (EVar "Cons") 
                     (EAp (EAp (EVar "f") (EVar "a")) (EVar "b"))) 
                (EAp (EAp (EAp (EVar "zipWith") (EVar "f")) (EVar "as")) 
                     (EVar "bs"))),
        ("foldr", ["f","x0","xs"],
            EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "x0")) 
                (EAp (EAp (EVar "prFoldr") (EVar "f")) (EVar "x0"))),
        ("prFoldr", ["f","a0","a","as"],
            EAp (EAp (EVar "f") (EVar "a")) 
                (EAp (EAp (EAp (EVar "foldr") (EVar "f")) (EVar "a0")) 
                     (EVar "as"))),
        ("foldl", ["f","x0","xs"],
            EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "x0")) 
            (EAp (EAp (EVar "prFoldl") (EVar "f")) (EVar "x0"))),
        ("prFoldl", ["f","a0","a","as"],
            EAp (EAp (EAp (EVar "foldl") (EVar "f")) 
                     (EAp (EAp (EVar "f") (EVar "a0")) (EVar "a"))) 
                (EVar "as")),
        ("take", ["n", "as"],
            EAp (EAp (EAp (EVar "caseList") (EVar "as")) (EVar "Nil")) 
                (EAp (EVar "prTake") (EVar "n"))),
        ("prTake", ["n", "a", "as"],
            EAp (EAp (EAp (EVar "if") 
                          (EAp (EAp (EVar ">") (EVar "n")) (ENum 0)))
                     (EAp (EAp (EVar "Cons") (EVar "a")) 
                          (EAp (EAp (EVar "take") 
                                    (EAp (EAp (EVar "-") (EVar "n")) 
                                         (ENum 1))) 
                               (EVar "as")))) 
                (EVar "Nil"))]

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
                        isDataNode (hLookup heap soleAddr)
                    [] -> error "empty stack!"
                    stack -> False

-- | is this node a data node?
isDataNode :: Node -> Bool
isDataNode node = case node of
    NNum _ -> True
    NData _ _ -> True
    _ -> False

-- | advance one step of the state
advanceState :: TiState -> TiState
advanceState state@(addr:stack, dump, heap, globals, stat) =
    case hLookup heap addr of
        NAp a1 a2 -> apStep a1 a2 state
        NSC name args body -> applyToStats tiStatsIncSR $
            scStep name args body state
        NNum _ -> numStep state
        NData _ _ -> dataStep state
        NInd aInd -> (aInd:stack, dump, heap, globals, stat)
        NConstr tag arity -> buildConstr tag arity state
        NPrim name primitive -> applyToStats tiStatsIncPR $
            prStep name primitive state

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
getArgs sc _ [] _ = nArgErr sc "few"
getArgs sc (name:args) (addr:stack) heap = (newStack, argList') 
    where argList' = aInsert (name, operand) argList
          NAp _ operand = hLookup heap addr
          (newStack, argList) = getArgs sc args stack heap

-- | argument number error message, the @String@ argument could be 
-- "many" or "few", indicates the how the error occurs
nArgErr :: Name -> String -> a
nArgErr name str = error $ name++ " is applied to too "++str++" arguments."

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
    EConstr tag arity -> hAlloc heap $ NConstr tag arity
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
    EConstr tag arity -> hUpdate heap addr $ NConstr tag arity
    ELet flag defs body -> 
        instantiateAndUpdateLet flag defs body addr heap varList
    ELam vars body -> error "Can't instantiate lambda expression yet."

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
numStep ([addr], stack:dump, heap, globals, stats) = 
    ([last stack], dump, heap, globals, stats)
numStep _ = error "Number can not apply to anything."

dataStep :: TiState -> TiState
dataStep ([addr], stack:dump, heap, globals, stats) = 
    ([last stack], dump, heap, globals, stats)
dataStep _ = error "Data constructor has too many arguments."

-- | a function advancing one step when the head of stack points to 
-- a primitive operation
prStep :: Name -> Primitive -> TiState -> TiState
prStep name primitive = case primitive of 
    Neg -> primArith1 name negate
    Add -> primArith2 name (+) 
    Sub -> primArith2 name (-) 
    Mul -> primArith2 name (*) 
    Div -> primArith2 name div 
    Lt -> primCompare name (<) 
    Eq -> primCompare name (==)
    Gt -> primCompare name (>) 
    Leq -> primCompare name (<=)
    Neq -> primCompare name (/=) 
    Geq -> primCompare name (>=)
    CaseBool -> primIf 
    CasePair -> primPair
    CaseList -> primList
    Abort -> error "empty list"
    Print -> primPrint

primUnary :: Name -> (Node -> Node) -> TiState -> TiState
primUnary name _ ([prim], _, _, _, _) = nArgErr name "few"
primUnary _ func (prim:[ap], dump, heap, globals, stats)
    | isDataNode oprNode = 
        ([ap], dump, hUpdate heap ap (func oprNode), globals, stats)
    | otherwise = ([operand], [prim,ap]:dump, heap, globals, stats)
        where NAp _ operand = hLookup heap ap
              oprNode = hLookup heap operand
primUnary name _ _ = nArgErr name "many"

primBinary :: Name -> (Node -> Node -> Node) -> TiState -> TiState
primBinary name _ ([prim], _, _, _, _) = nArgErr name "few"
primBinary name _ ([prim, ap], _, _, _, _) = nArgErr name "few"
primBinary name func (prim:[ap1,ap2], dump, heap, globals, stats)
    | isDataNode oprNode = primUnary name (func oprNode)
        ([ap1,ap2], dump, heap, globals, stats)
    | otherwise = ([operand], [prim,ap1,ap2]:dump, heap, globals, stats)
        where NAp _ operand = hLookup heap ap1
              oprNode = hLookup heap operand
primBinary name _ _ = nArgErr name "many"

primArith1 :: Name -> (Int -> Int) -> TiState -> TiState
primArith1 name func = primUnary name funcNode
    where funcNode (NNum x) = NNum (func x)

primArith2 :: Name -> (Int -> Int -> Int) -> TiState -> TiState
primArith2 name func = primBinary name funcNode
    where funcNode (NNum x) (NNum y) = NNum $ func x y

-- | take the operand address of the given NAp node
takeOpr :: TiHeap -> Addr -> Addr
takeOpr heap addr = let (NAp _ opr) = hLookup heap addr in opr

buildConstr :: Int -> Int -> TiState -> TiState
buildConstr tag arity (stack, dump, heap, globals, stats) = 
    (drop arity stack, dump, newHeap, globals, stats)
    where newHeap = hUpdate heap (stack!!arity) (NData tag pars)
          pars 
            | length stack > arity = 
                take arity $ map (takeOpr heap) (tail stack)
            | otherwise = nArgErr "Data Constructor" "few"

primCompare :: Name -> (Int -> Int -> Bool) -> TiState -> TiState
primCompare name func = primBinary name funcNode
    where funcNode (NNum x) (NNum y) = NData (2 - fromEnum (func x y)) []

-- | apply the if primitive to transit state
primIf :: TiState -> TiState
primIf (stack@[_, _, _, ap3], dump, heap, globals, stats) = 
    case hLookup heap bool of
        NData tag _ -> ([ap3], dump, newHeapWith tag, globals, stats)
        _ -> ([bool], stack:dump, heap, globals, stats)
    where pars@[bool, _, _] = map (takeOpr heap) (tail stack)
          newHeapWith ind = hUpdate heap ap3 $ hLookup heap (pars!!ind)
primIf (stack, _, _, _, _)
    | length stack < 4 = nArgErr "if" "few"
    | otherwise = nArgErr "if" "many"

primPair :: TiState -> TiState
primPair (stack@[_, _, apr], dump, heap, globals, stats) =
    let [pair, f] = map (takeOpr heap) (tail stack) 
    in case hLookup heap pair of
        NData 1 [p1, p2] -> ([apr], dump, newHeap, globals, stats)
            where newHeap = hUpdate tmpHeap apr $ NAp ap1 p2
                  (tmpHeap, ap1) = hAlloc heap $ NAp f p1
        _ -> ([pair], stack:dump, heap, globals, stats)
primPair (stack, _, _, _, _)
    | length stack < 3 = nArgErr "Pair" "few"
    | otherwise = nArgErr "Pair" "many"

primList :: TiState -> TiState
primList (stack@[_, _, _, apr], dump, heap, globals, stats) =
    let [ls, cn, cc] = map (takeOpr heap) (tail stack)
    in case hLookup heap ls of
        NData 1 _ -> ([apr], dump, newHeap, globals, stats)
            where newHeap = hUpdate heap apr $ hLookup heap cn
        NData 2 [ah, at] -> ([apr], dump, newHeap, globals, stats)
            where newHeap = hUpdate tmpHeap apr $ NAp ap1 at
                  (tmpHeap, ap1) = hAlloc heap $ NAp cc ah
        _ -> ([ls], stack:dump, heap, globals, stats)    
primList (stack, _, _, _, _)
    | length stack < 4 = nArgErr "list function" "few"
    | otherwise = nArgErr "list function" "many"

primPrint :: TiState -> TiState
primPrint (stack@[_, apr], dump, heap, globals, stats) = 
    let ls = takeOpr heap apr
    in case hLookup heap ls of
        NData 1 _ -> ([ls], dump, heap, globals, stats)
        NData 2 [ah, at] -> 
            case hLookup heap ah of
                NNum num -> (stack, dump, newHeap, globals, newStats)
                    where newHeap = hUpdate heap ls $ hLookup heap at
                          newStats = tiStatsOutput (num:) stats
                _ -> ([ah], stack:dump, heap, globals, stats)
        _ -> ([ls], stack:dump, heap, globals, stats)
primPrint (stack, _, _, _, _)
    | length stack < 2 = nArgErr "print" "few"
    | otherwise = nArgErr "print" "many"

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
      NInd addr -> cStr "NInd" `cAppend` cLPNum 3 addr
      NConstr t a -> cConcat [ cStr "NConstr", cLPNum 2 t, cLPNum 2 a]
      NPrim prim _ -> cStr "NPrim " `cAppend` cStr prim
      NData tag pars -> 
        cConcat [cStr "NData ", cNum tag, cStr " ", cStr $ show pars ] 
    ]

pprStatsInState :: TiState -> Cseq
pprStatsInState (_, _, heap, _, stats) = cConcat 
    [   cStr "Output:", cStr . show . reverse . output $ stats, cNewline,
        cStr "This program takes ", cNum $ steps stats, 
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
                

