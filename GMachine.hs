------------------------------------------------------------------------------
--
-- | 
-- Module   : CoreLanguage.GMachine
--
-- A graph reducer based on g-machine, which complies all supercombinators to
-- instructions (equivalently, postfix expressions) before evaluation.
--
------------------------------------------------------------------------------


module CoreLanguage.GMachine (

    -- * run the program
    run

    ) where

import CoreLanguage.Base
import CoreLanguage.Parser
import CoreLanguage.Utility

-- | the state used in g-machine
type GmState = (GmCode, GmStack, GmDump, GmHeap, GmGlobals, GmStats)

-- | GmCode is a sequence of instructions
type GmCode = [Instruction]

-- | The Instruction Set of G-Machine 
--
--  * @PushGlobal name@ push the address of the given supercombinator in stack
--  * @Push n@ take a copy of \n\th argument which passed to a function
--  * @PushInt num@ places an integer node in heap
--  * @Mkap@ take top two addresses in stack and make them 
--      a function application
--  * @Slide n@ pulls off n addresses under the top of stack
--  * @Update n@ updates the root node to an indirection node pointing to 
--      the newly instanted supercombinator
--  * @Pop n@ simply pops n items off the stack
--  * @Unwind@ 
--  * @Alloc n@ puts n indirection nodes on top of stack
--  * @Eval@ will evaluate the head of stack to WHNF
--  * Arithmetic operations
--  * Comparison operations
--  * @Cond code1 code2@ acts like if expression
data Instruction    = PushGlobal Name
                    | Push Int
                    | PushInt Int 
                    | Mkap
                    | Slide Int
                    | Update Int
                    | Pop Int
                    | Unwind
                    | Alloc Int
                    | Eval
                    | Neg | Add | Sub | Mul | Div
                    | Eq | Neq | Lt | Gt | Leq | Geq
                    | Null
    deriving (Eq, Show)

getCode :: GmState -> GmCode
getCode (c,_,_,_,_,_) = c

putCode :: GmCode -> GmState -> GmState
putCode c' (c, sk, d, h, g, ss) = (c', sk, d, h, g, ss)

type GmStack = [Addr]

getStack :: GmState -> GmStack
getStack (_,s,_,_,_,_) = s

putStack :: GmStack -> GmState ->GmState
putStack sk' (c, sk, d, h, g, ss) = (c, sk', d, h, g, ss)

type GmDump = [(GmCode, GmStack)]

getDump :: GmState -> GmDump
getDump (_,_,d,_,_,_) = d

putDump :: GmDump -> GmState -> GmState
putDump d' (c, sk, d, h, g, ss) = (c, sk, d', h, g, ss)

type GmHeap = Heap Node

getHeap :: GmState -> GmHeap
getHeap (_,_,_,h,_,_) = h

putHeap :: GmHeap -> GmState -> GmState
putHeap h' (c, sk, d, h, g, ss) = (c, sk, d, h', g, ss)

-- | the supercombinator node now stores numbers of arguments taken and
-- instructions, differs from that in tempelate instantiation machine
data Node   = NAp Addr Addr
            | NNum Int
            | NGlobal Int GmCode
            | NInd Int

type GmGlobals = Assocs Name Addr

getGlobals :: GmState -> GmGlobals
getGlobals (_,_,_,_,g,_) = g

data GmStats = GmStep   { step :: Int
                         ,maxStk :: Int
                         ,maxDmp :: Int
                        }

gmStatsInit :: GmStats
gmStatsInit = GmStep 0 0 0

gmStatsIncStep :: GmStats -> GmStats
gmStatsIncStep (GmStep n x y) = GmStep (n+1) x y

gmStatsChangeMaxStk :: Int -> GmStats -> GmStats
gmStatsChangeMaxStk n' (GmStep x n y) = GmStep x n' y

gmStatsChangeMaxDmp :: Int -> GmStats -> GmStats
gmStatsChangeMaxDmp n' (GmStep x y n) = GmStep x y n'

getStats :: GmState -> GmStats
getStats (_,_,_,_,_,ss) = ss

putStats :: GmStats -> GmState -> GmState
putStats ss' (c, sk, d, h, g, ss) = (c, sk, d, h, g, ss')

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- | @run@ the program!
run :: String -> String
run = showResult . eval . compile . parse

------------------------------------------------------------------------------

-- | compile the abstract syntax tree into an initail state, mainly turn 
-- supercombinators into instructions
compile :: CoreProgram -> GmState
compile prog = (initialCode, [], [], initialHeap, globals, gmStatsInit)
    where initialCode = [PushGlobal "main", Unwind]
          globals = aFromList tmpGlobals
          (initialHeap, tmpGlobals) = mapAccuml allocateSc hInitial compiled
          compiled = map compileSc (prog++preludeDefs) ++ compiledPrim
          allocateSc heap (name, nargs, code) = 
            let (newHeap, addr) = hAlloc heap (NGlobal nargs code)
            in (newHeap, (name, addr))

compileSc :: CoreScDef -> (Name, Int, GmCode)
compileSc (name, args, body) = (name, scArity, code)
    where code = compileExprStrict 0 args body ++ 
            [Update scArity, Pop scArity, Unwind]
          scArity = length args

compileExpr :: Int -> [Name] -> CoreExpr -> GmCode
compileExpr depth args expr = case expr of
    ENum num -> [PushInt num]
    EVar x
        | nAg >= 0 -> [Push (nAg+depth)]
        | otherwise -> [PushGlobal x]
            where nAg = findIndex x args
    EAp f x ->  compileExpr depth args x ++ 
        compileExpr (depth+1) args f ++ [Mkap]
    ELet isRec bindings body -> 
        compileLet isRec bindings body depth args

compileExprStrict :: Int -> [Name] -> CoreExpr -> GmCode
compileExprStrict depth args expr = 
    case expr of 
        ENum num -> [PushInt num]
        EAp (EAp (EVar f) a) b 
            | ins /= Null ->  
                compileExprStrict depth args b ++ 
                compileExprStrict (depth+1) args a ++
                [ins]
            | otherwise -> compileExpr depth args expr ++ [Eval]
            where ins = aLookup builtinBinOp f Null
        EAp (EVar "negate") x -> compileExprStrict depth args x ++ [Neg]
        ELet isRec bindings body -> 
            compileLetStrict isRec bindings body depth args
        _ -> compileExpr depth args expr ++ [Eval]
    
compileLet  :: IsRec -> [(Name, CoreExpr)] -> CoreExpr  
            -> Int -> [Name] -> GmCode
compileLet isRec bindings body depth args
    | isRec == nonRecursive = concat (
        zipWith (`compileExpr` args) [depth ..] (reverse defs))
        ++ compileWithDefs body ++ [Slide nDefs]
    | isRec == recursive = [Alloc nDefs] 
        ++ concat (zipWith (++) (map compileWithDefs defs) 
            (map (\n -> [Update n]) [0..(nDefs-1)]))
        ++ compileWithDefs body ++ [Slide nDefs]
        where nDefs = length bindings
              defs = rhssOf bindings
              compileWithDefs = compileExpr 0 
                (bindersOf bindings ++ replicate depth "_" ++ args)

compileLetStrict    :: IsRec -> [(Name, CoreExpr)] -> CoreExpr  
                    -> Int -> [Name] -> GmCode
compileLetStrict isRec bindings body depth args
    | isRec == nonRecursive = concat (
        zipWith (`compileExpr` args) [depth ..] (reverse defs))
        ++ cwds body ++ [Slide nDefs]
    | isRec == recursive = [Alloc nDefs] 
        ++ concat (zipWith (++) 
            (map (compileExpr 0 args') defs)
            (map (\n -> [Update n]) [0..(nDefs-1)]))
        ++ cwds body ++ [Slide nDefs]
        where nDefs = length bindings
              defs = rhssOf bindings
              cwds = compileExprStrict 0 args'
              args' = bindersOf bindings ++ replicate depth "_" ++ args

-- | return the index of specific element first appears in a list, 
-- and return -1 if element not in the list
findIndex :: Eq a => a -> [a] -> Int
findIndex e es = go e es
    where go x [] = - length es - 1
          go x (y:ys)
            | x==y = 0
            | otherwise = 1 + go x ys

compiledPrim :: [(Name, Int, GmCode)]
compiledPrim = [
    ("negate", 1, [Push 0, Eval, Neg, Update 1, Pop 1, Unwind]),
    ("+", 2, [Push 1, Eval, Push 1, Eval, Add, Update 2, Pop 2, Unwind]),
    ("-", 2, [Push 1, Eval, Push 1, Eval, Sub, Update 2, Pop 2, Unwind]),
    ("*", 2, [Push 1, Eval, Push 1, Eval, Mul, Update 2, Pop 2, Unwind]),
    ("/", 2, [Push 1, Eval, Push 1, Eval, Div, Update 2, Pop 2, Unwind]) ]

builtinBinOp :: Assocs Name Instruction
builtinBinOp = aFromList [   
    ("+", Add), ("-", Sub), ("*", Mul), ("/", Div), ("<", Lt), ("==", Eq), 
    (">", Gt), ("<=", Leq), (">=", Geq), ("/=", Neq) ]

------------------------------------------------------------------------------

-- | push forward states
eval :: GmState -> [GmState]
eval state = state : followingStates
    where followingStates
            | gmFinal state = []
            | otherwise = eval . doAdmin . advanceStep $ state 

-- | test for fianl state
gmFinal :: GmState -> Bool
gmFinal state = case getCode state of
                  [] -> True
                  codes -> False

-- | log the performance statistics
doAdmin :: GmState -> GmState
doAdmin state = putStats (gmStatsIncStep.f.g $ stats) state
    where stats = getStats state
          f | csd<sd = gmStatsChangeMaxStk sd | otherwise =  id
          g | cdd<dd = gmStatsChangeMaxDmp dd | otherwise =  id
          csd = maxStk stats
          sd = length $ getStack state
          cdd = maxDmp stats
          dd = length $ getDump state

advanceStep :: GmState -> GmState
advanceStep state = 
    let (ins:code) = getCode state
        stack = getStack state
        dump = getDump state
        heap = getHeap state
        globals = getGlobals state
        newState = putCode code state
    in case ins of
        PushGlobal name -> 
            let err = error $ "can't find defination of "++name 
            in putStack (aLookup globals name err : stack) newState
        PushInt num -> 
            let (newHeap, addr) = hAlloc heap (NNum num) 
            in putHeap newHeap $ putStack (addr:stack) newState
        Push n ->  putStack ((stack!!n):stack) newState
        Mkap -> let (newHeap, addr) = hAlloc heap (NAp a1 a2)
                    a1:a2:stack' = stack
                    newStack = addr:stack'
                in putStack newStack $ putHeap newHeap newState
        Slide n -> let (a:as) = stack
                   in putStack (a : drop n as) newState
        Update n -> let (a:as) = stack in putStack as $ 
            putHeap (hUpdate heap (stack !! (n+1)) (NInd a)) newState
        Pop n -> putStack (drop n stack) newState
        Unwind -> unwind newState
        Alloc n -> let (newHeap, as) = mapAccuml hAlloc heap $
                            replicate n (NInd hNull)
                   in putStack (as++stack) $ putHeap newHeap newState
        Eval -> let (a:as) = stack in putCode [Unwind] . 
                    putDump ((code,as):dump) . putStack [a] $ state
        prims -> primStep prims newState

unwind :: GmState -> GmState
unwind state = case hLookup (getHeap state) addr of
    NNum num -> case getDump state of
        (c,s):ds -> putDump ds . putCode c . putStack (addr:s) $ state
        _ -> state
    NAp a1 a2 -> putCode [Unwind] $ putStack (a1:stack) state
    NGlobal n code
        | length stack < n -> error "not enough arguments"
        | otherwise -> putCode code $ rearrange n state
    NInd aInd -> putCode [Unwind] $ putStack (aInd:as) state
    where stack@(addr:as) = getStack state

rearrange :: Int -> GmState -> GmState
rearrange n state = putStack newStack state
    where newStack = map takeOpr (take n (tail stack)) ++ drop n stack
          stack = getStack state
          takeOpr addr = let NAp _ opr = hLookup (getHeap state) addr in opr

-- | put an integer into heap and insert its address in top of stack
boxInteger :: Int -> GmState -> GmState
boxInteger n state = putStack (addr: getStack state) $ putHeap newHeap state
    where (newHeap, addr) = hAlloc (getHeap state) (NNum n)

-- | extract an integer at specific address
unboxInteger :: Addr -> GmState -> Int
unboxInteger addr state = ub $ hLookup (getHeap state) addr
    where ub (NNum num) = num
          ub _ = error "Unboxing a non-interger"

primUnary   :: (b -> GmState -> GmState) 
            -> (Addr -> GmState -> a) 
            -> (a -> b) -> GmState -> GmState
primUnary box unbox op state = let (a:as) = getStack state in
    box (op $ unbox a state) (putStack as state)

primBinary  :: (b -> GmState -> GmState) 
            -> (Addr -> GmState -> a) 
            -> (a -> a -> b) -> GmState -> GmState
primBinary box unbox op state = let (a0:a1:as) = getStack state in
    box (op (unbox a0 state) (unbox a1 state)) (putStack as state)

primArith1 :: (Int -> Int) -> GmState -> GmState
primArith1 = primUnary boxInteger unboxInteger 

primArith2 :: (Int -> Int -> Int) -> GmState -> GmState
primArith2 = primBinary boxInteger unboxInteger

primStep :: Instruction -> GmState -> GmState
primStep prim = case prim of
    Neg -> primArith1 negate
    Add -> primArith2 (+)
    Sub -> primArith2 (-)
    Mul -> primArith2 (*)
    Div -> primArith2 div

------------------------------------------------------------------------------

-- | formatting the output
showResult :: [GmState] -> String
showResult states@(s:_) = cToStr $ cConcat [
    cStr "Supercombinator Definations", cNewline,
    cIntercalate cNewline $ map (pprSc heap) (aToList globals),
    cNewline, cNewline, 
    cStr "States Transition", cNewline,
    cNumList (map pprState states), cNewline, 
    cStr "Performance Statistics", cNewline, 
    pprStatistics (last states) ]
    where heap = getHeap s
          globals = getGlobals s

pprSc :: GmHeap -> (Name, Addr) -> Cseq
pprSc heap (name, addr) = cConcat [ 
    cStr ("Code for "++name), cNewline, cStr "  ", cIndent $ pprCode code ]
    where NGlobal _ code = hLookup heap addr

pprCode :: GmCode -> Cseq
pprCode = cIntercalate cNewline . map pprInstruction

pprInstruction :: Instruction -> Cseq
pprInstruction = cStr . show

pprState :: GmState -> Cseq
pprState (code, stack, dump, heap, globals, _) = cConcat [   
    cStr "Instructions:", cNewline, 
    cStr "  ", cIndent $ pprCode code, cNewline,
    cStr "Stack:", cNewline, 
    cIntercalate cNewline $ 
        pprNode <$> reverse stack <*> pure heap <*> pure globals ]

pprNode :: Addr -> GmHeap -> GmGlobals -> Cseq
pprNode addr heap globals = cConcat [ cLPNum 3 addr, cStr " -> ",
    case hLookup heap addr of
        NAp a1 a2 -> cConcat [ cStr "Ap", cLPNum 4 a1, cLPNum 4 a2  ]
        NGlobal _ _ -> let name:_ = [ n | (n,a) <- aToList globals, a==addr]
                       in cStr ("Supercombinator "++name)
        NNum num -> cStr "Num " `cAppend` cNum num
        NInd addr -> cStr "Indirection to " `cAppend` cNum addr
    ]

pprStatistics :: GmState -> Cseq
pprStatistics state = cConcat [   
    cStr "Steps taken is ", cNum $ step stats, cNewline,
    cStr "Max Stack Depth is ", cNum $ maxStk stats, cNewline,
    cStr "Max Dump Depth is ", cNum $ maxDmp stats]
    where stats = getStats state

