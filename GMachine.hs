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
type GmState = (GmCode, GmStack, GmHeap, GmGlobals, GmStats)

-- | GmCode is a sequence of instructions
type GmCode = [Instruction]

-- | There are seven instructions
--
--  * @PushGlobal name@ push the address of the given supercombinator in stack
--  * @Push n@ take a copy of \n\th argument which passed to a function
--  * @PushInt num@ places an integer node in heap
--  * @Mkap@ take top two addresses in stack and make them 
--      a function application
--  * @Update n@ updates the root node to an indirection node pointing to 
--      the newly instanted supercombinator
--  * @Pop n@ simply pops n items off the stack
--  * @Unwind@ 
data Instruction    = PushGlobal Name
                    | Push Int
                    | PushInt Int 
                    | Mkap
                    | Update Int
                    | Pop Int
                    | Unwind
    deriving (Eq, Show)

getCode :: GmState -> GmCode
getCode (c,_,_,_,_) = c

putCode :: GmCode -> GmState -> GmState
putCode c' (c, sk, h, g, ss) = (c', sk, h, g, ss)

type GmStack = [Addr]

getStack :: GmState -> GmStack
getStack (_,s,_,_,_) = s

putStack :: GmStack -> GmState ->GmState
putStack sk' (c, sk, h, g, ss) = (c, sk', h, g, ss)

type GmHeap = Heap Node

getHeap :: GmState -> GmHeap
getHeap (_,_,h,_,_) = h

putHeap :: GmHeap -> GmState -> GmState
putHeap h' (c, sk, h, g, ss) = (c, sk, h', g, ss)

-- | the supercombinator node now stores numbers of arguments taken and
-- instructions, differs from that in tempelate instantiation machine
data Node   = NAp Addr Addr
            | NNum Int
            | NGlobal Int GmCode
            | NInd Int

type GmGlobals = Assocs Name Addr

getGlobals :: GmState -> GmGlobals
getGlobals (_,_,_,g,_) = g

data GmStats = GmStep   { step :: Int
                         ,maxStk :: Int
                        }

gmStatsInit :: GmStats
gmStatsInit = GmStep 0 0

gmStatsIncStep :: GmStats -> GmStats
gmStatsIncStep (GmStep n x) = GmStep (n+1) x

gmStatsChangeMaxStk :: Int -> GmStats -> GmStats
gmStatsChangeMaxStk n' (GmStep x n) = GmStep x n'

getStats :: GmState -> GmStats
getStats (_,_,_,_,ss) = ss

putStats :: GmStats -> GmState -> GmState
putStats ss' (c, sk, h, g, ss) = (c, sk, h, g, ss')

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- | @run@ the program!
run :: String -> String
run = showResult . eval . compile . parse

------------------------------------------------------------------------------

-- | compile the AST into an initail state
compile :: CoreProgram -> GmState
compile prog = (initialCode, [], initialHeap, globals, gmStatsInit)
    where initialCode = [PushGlobal "main", Unwind]
          globals = aFromList tmpGlobals
          (initialHeap, tmpGlobals) = mapAccuml allocateSc hInitial compiled
          compiled = map compileSc (prog++preludeDefs) ++ compiledPrim
          allocateSc heap (name, nargs, code) = 
            let (newHeap, addr) = hAlloc heap (NGlobal nargs code)
            in (newHeap, (name, addr))

compileSc :: CoreScDef -> (Name, Int, GmCode)
compileSc (name, args, body) = (name, scArity, code)
    where code = compileExpr 0 args body ++ 
            [Update scArity, Pop scArity, Unwind]
          scArity = length args

compileExpr :: Int -> [Name] -> CoreExpr -> GmCode
compileExpr depth args expr = case expr of
    ENum num -> [PushInt num]
    EVar x
        | nAg > 0 -> [Push (nAg+depth)]
        | otherwise -> [PushGlobal x]
            where nAg = findIndex x args
    EAp f x ->  compileExpr depth args f ++ 
        compileExpr (depth+1) args x ++ [Mkap]

-- | return the index of specific element first appears in a list, 
-- and return 0 if element not in the list
findIndex :: Eq a => a -> [a] -> Int
findIndex e es = go e es
    where go x [] = - length es
          go x (y:ys)
            | x==y = 1
            | otherwise = 1 + go x ys

compiledPrim :: [(Name, Int, GmCode)]
compiledPrim = []

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
doAdmin state = putStats (gmStatsIncStep.f $ stats) state
    where stats = getStats state
          f | csd<sd = gmStatsChangeMaxStk sd | otherwise =  id
          csd = maxStk stats
          sd = length $ getStack state

advanceStep :: GmState -> GmState
advanceStep state = 
    let (ins:code) = getCode state
        stack = getStack state
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
        Push nth -> 
            let NAp _ addr = hLookup heap (stack!!nth)
            in putStack (addr:stack) newState
        Mkap -> let (newHeap, addr) = hAlloc heap (NAp a2 a1)
                    a1:a2:stack' = stack
                    newStack = addr:stack'
                in putStack newStack $ putHeap newHeap newState
        Update n -> putStack (tail stack) $ putHeap 
            (hUpdate heap (stack !! (n+1)) (NInd $ head stack)) newState
        Pop n -> putStack (drop n stack) newState
        Unwind -> unwind newState

unwind :: GmState -> GmState
unwind state = case hLookup heap addr of
    NNum num -> state
    NAp a1 a2 -> putCode [Unwind] $ putStack (a1:stack) state
    NGlobal n code
        | length stack < n -> error "not enough arguments"
        | otherwise -> putCode code $ putStack stack state
    NInd aInd -> putCode [Unwind] $ putStack (aInd:as) state
    where stack@(addr:as) = getStack state
          heap = getHeap state

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
pprState (code, stack, heap, globals, _) = cConcat [   
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
    cStr "Max Stack Depth is ", cNum $ maxStk stats]
    where stats = getStats state

