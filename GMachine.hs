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

-- | There are six instructions
--
--  * @PushGlobal name@ push the address of the given supercombinator in stack
--  * @Push n@ take a copy of \n\th argument which passed to a function
--  * @PushInt num@ places an integer node in heap
--  * @Mkap@ take top two addresses in stack and make them 
--      a function application
--  * @Slide num@ tidy up the stack after instantiation of a supercombinator
--  * @Unwind@  
data Instruction    = PushGlobal Name
                    | Push Int
                    | PushInt Int 
                    | Mkap
                    | Slide Int
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
            | NSC Int GmCode

type GmGlobals = Assocs Name Addr

getGlobals :: GmState -> GmGlobals
getGlobals (_,_,_,g,_) = g

data GmStats = GmStep   { step :: Int
                        }

gmStatsInit :: GmStats
gmStatsInit = GmStep 0

gmStatsIncStep :: GmStats -> GmStats
gmStatsIncStep (GmStep n) = GmStep (n+1)

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
compile prog = (mainCode, initialStack, initialHeap, globals, gmStatsInit)
    where initialStack = [mainAddr]
          globals = aFromList tmpGlobals
          (initialHeap, tmpGlobals) = mapAccuml buildHeap hInitial $
              prog ++ preludeDefs
          NSC _ mainCode = hLookup initialHeap mainAddr
          mainAddr = aLookup globals "main" (error "can't find main")

buildHeap :: GmHeap -> CoreScDef -> (GmHeap, (Name, Addr))
buildHeap heap (name, vars, body) = (newHeap, (name, addr))
    where (newHeap, addr) = hAlloc heap (NSC scArity code)
          code = rhssOf (compileExpr 0 vars body) ++ 
              [Slide (scArity+1), Unwind]
          scArity = length vars

compileExpr :: Int -> [Name] -> CoreExpr -> [(Int, Instruction)]
compileExpr depth vars expr = case expr of
    ENum num -> [(depth+1, PushInt num)]
    EVar x
        | nAg > 0 -> [(depth+1, Push (nAg+depth))]
        | otherwise -> [(depth+1, PushGlobal x)]
            where nAg = nthArg x vars
    EAp f x ->  let fIns = compileExpr depth vars f
                    xIns = compileExpr fd vars x
                    (fd,_) = last fIns
                    (xd,_) = last xIns
                in fIns ++ xIns ++ [(xd-1, Mkap)]
    where nthArg x [] = - length vars
          nthArg x (v:vs)
            | x==v = 1
            | otherwise = 1 + nthArg x vs

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
doAdmin state = putStats (gmStatsIncStep $ getStats state) state

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
        Slide n -> let (a:as) = stack
                   in putStack (a : drop n as) newState
        Unwind -> unwind newState

unwind :: GmState -> GmState
unwind state = case hLookup heap addr of
    NNum num -> state
    NAp a1 a2 -> putCode [Unwind] $ putStack (a1:stack) state
    NSC n code
        | length stack < n -> error "not enough arguments"
        | otherwise -> putCode code $ putStack stack state
    where stack@(addr:_) = getStack state
          heap = getHeap state

------------------------------------------------------------------------------

-- | formatting the output
showResult :: [GmState] -> String
showResult states = cToStr $
    cNumList (map pprState states) `cAppend` pprStatsInState (last states)

pprState :: GmState -> Cseq
pprState (code, stack, heap, _, _) = 
    cConcat [   pprInstructions code, cNewline, 
                cIntercalate cNewline $ pprNode <$> stack <*> pure heap ]

pprInstructions :: GmCode -> Cseq
pprInstructions [] = cStr "End"
pprInstructions ins = cStr . show . head $ ins

pprNode :: Addr -> GmHeap -> Cseq
pprNode addr heap = cConcat [ cLPNum 3 addr, cStr ": ",
    case hLookup heap addr of
        NAp a1 a2 -> cConcat [ cStr "NAp", cLPNum 4 a1, cLPNum 4 a2  ]
        NSC _ _ -> cStr "supercombinator"
        NNum num -> cStr "NNum " `cAppend` cNum num
    ]

pprStatsInState :: GmState -> Cseq
pprStatsInState state = 
    cConcat [   cStr "This program takes ",
                cNum . step . getStats $ state,
                cStr " steps." ]


