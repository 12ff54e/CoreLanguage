------------------------------------------------------------------------------
--
-- | 
-- Module   : CoreLanguage.TIM
--
-- A tree reducer based on three instruction machine (TIM). It "flattens" all
-- supercombinators and pack its variables, thus only three main instructions 
-- are needed.
--
------------------------------------------------------------------------------

module TIM where

import Base
import Utility
import Parser

-- | the state used in TIM
data TimState = TimState {
    currentCode :: [Instruction],
    framePtr :: FramePtr,
    stack :: TimStack,
    valueStack :: TimValueStack,
    dump :: TimDump,
    heap :: TimHeap,
    codeStore :: TimCodeStore,
    stats :: TimStats
}

setCurrentCode :: [Instruction] -> TimState -> TimState
setCurrentCode code (TimState _ fp stack vstack dump heap cs stats) = 
    TimState code fp stack vstack dump heap cs stats

setFramePtr :: FramePtr -> TimState -> TimState
setFramePtr fp (TimState cc _ stack vstack dump heap cs stats) = 
    TimState cc fp stack vstack dump heap cs stats

setStack :: TimStack -> TimState -> TimState
setStack stack (TimState cc fp _ vstack dump heap cs stats) =
    TimState cc fp stack vstack dump heap cs stats

setVStack :: TimValueStack -> TimState -> TimState
setVStack vstack (TimState cc fp stack _ dump heap cs stats) =
    TimState cc fp stack vstack dump heap cs stats

setDump :: TimDump -> TimState -> TimState
setDump dump (TimState cc fp stack vstack _ heap cs stats) =
    TimState cc fp stack vstack dump heap cs stats

setHeap :: TimHeap -> TimState -> TimState
setHeap heap (TimState cc fp stack vstack dump _ cs stats) = 
    TimState cc fp stack vstack dump heap cs stats

setCodeStore :: TimCodeStore -> TimState -> TimState
setCodeStore cs (TimState cc fp stack vstack dump heap _ stats) = 
    TimState cc fp stack vstack dump heap cs stats

setStats :: TimStats -> TimState -> TimState
setStats stats (TimState cc fp stack vstack dump heap cs _) = 
    TimState cc fp stack vstack dump heap cs stats

-- | Instruction Set
data Instruction    = Take Int
                    | Push TimAddr
                    | Enter TimAddr

-- | Address data type used in TIM
data TimAddr    = Arg Int
                | Labal String
                | Code [Instruction]
                | IntConst Int

-- | pointer to Frame in heap, but it can also hold an Integer inside it
data FramePtr   = FrameAddr Addr
                | FrameInt Int
                | FrameNull

-- | stack stores closures
type TimStack = [Closure]

-- | closure is a tuple of code and Frame pointer
type Closure = ([Instruction], FramePtr)

-- | Value stack store numbers and bools
data TimValueStack = DummyVS

-- | Dump 
data TimDump = DummyD

-- | heap stores frames
type TimHeap = Heap Frame

-- | Frame is a list of closures
type Frame = [Closure]

-- | reload of @hAlloc@, return @FramePtr@ instead of @Addr@
fAlloc :: TimHeap -> Frame -> (TimHeap, FramePtr)
fAlloc heap frame = let (newHeap, addr) = hAlloc heap frame
                    in  (newHeap, FrameAddr addr)

-- | reload of @hLookup@, use @FramePtr@ to search frame in heap,
-- then take @n@-th closure in the frame
fGet :: TimHeap -> FramePtr -> Int -> Closure
fGet heap (FrameAddr addr) n = hLookup heap addr !! (n-1)
fGet heap _ n = undefined

-- | reload of @hUpdate@, use @FramePtr@ to search for the 
-- to-be-update frame
fUpdate :: TimHeap -> Frame -> FramePtr -> TimHeap
fUpdate heap frame (FrameAddr addr) = hUpdate heap addr frame
fUpdate heap frame _ = undefined

-- | for printing
fList :: Frame -> [Closure]
fList = id

-- | CodeStore links label and its code
type TimCodeStore = Assocs Name [Instruction]

codeLookup :: TimCodeStore -> Name -> [Instruction]
codeLookup cs label = 
    aLookup cs label $ error ("Labal " ++ show label ++ " undefined.")

-- | statistics
data TimStats = TimStats {
    step :: Int,
    maxStackDepth :: Int,
    heapLog :: (Int, Int), 
        -- Heap allocation time of last step, heap allocation of closures
    execTime :: Int
}

statsInitial :: TimStats
statsInitial = TimStats 0 0 (0, 0) 0

-- | set step in statistics, similar functions in the following
statsSetStep :: Int -> TimStats -> TimStats
statsSetStep n (TimStats x y z w) = TimStats n y z w

statsSetMSD :: Int -> TimStats -> TimStats
statsSetMSD n (TimStats x y z w) = TimStats x n z w

statsSetHL :: (Int, Int) -> TimStats -> TimStats
statsSetHL n (TimStats x y z w) = TimStats x y n w

statsSetET :: Int -> TimStats -> TimStats
statsSetET n (TimStats x y z w) = TimStats x n z n

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- | @run@ the program, transform source file to result
run :: String -> String
run = showResult . eval . compile . parse

-- | this function output infomation of prints every step
fullRun :: String -> String
fullRun = showFullResult . eval . compile . parse

------------------------------------------------------------------------------

-- | compile the AST into an initial state
compile :: CoreProgram -> TimState
compile prog = TimState 
    codeInitial
    FrameNull
    stackInitial
    valueStackInitial
    dumpInitial
    hInitial
    codeStoreInitial
    statsInitial
        where   codeInitial = [Enter (Labal "main")]
                codeStoreInitial = 
                    aFromList $ map (compileSc env) (prog ++ preludeDefs)
                -- env stores supercombinator names
                env = [(name, Labal name) | 
                    (name, _, _) <- prog ++ preludeDefs]

stackInitial :: TimStack
stackInitial = []

valueStackInitial :: TimValueStack
valueStackInitial = DummyVS

dumpInitial :: TimDump
dumpInitial = DummyD

compileSc :: [(Name, TimAddr)] -> CoreScDef -> (Name, [Instruction])
compileSc env (name, args, expr) = (name, code)
    where   code
                | null args = cc
                | otherwise = Take (length args) : cc
            cc = compileExpr (aFromList $ zip args (map Arg [1..]) ++ env) expr

compileExpr :: Assocs Name TimAddr -> CoreExpr -> [Instruction]
compileExpr env expr = case expr of
    ENum n -> [Enter (IntConst n)]
    EVar x -> [Enter (addressing env expr)]
    EAp e1 e2 -> Push (addressing env e2) : compileExpr env e1

addressing :: Assocs Name TimAddr -> CoreExpr -> TimAddr
addressing env expr = case expr of
    ENum n -> IntConst n
    EVar x -> aLookup env x $ defErr x
    _ -> Code $ compileExpr env expr

defErr :: Name -> a
defErr x = error $ "undefined variable " ++ show x ++ "!"

------------------------------------------------------------------------------

-- | push forward states
eval :: TimState -> [TimState]
eval state = state : subsequentStates
    where subsequentStates
            | timFinal state = []
            | otherwise = eval . advance . statsLog $ state 

statsLog :: TimState -> TimState
statsLog state = statsLogHeap $ setStats newStats state
    where   oldStats@(TimStats x y z w) = stats state
            newStats = statsSetStep (x+1) . statsSetMSD sd .
                statsSetET et $ oldStats
            sd = max y (length $ stack state)
            et = case head (currentCode state) of
                    Take n -> w + n
                    _ -> w + 1

statsLogHeap :: TimState -> TimState
statsLogHeap state = setStats newStats state
    where   newStats = statsSetHL (a, b) (stats state)
            (x, y) = heapLog $ stats state
            a = hGetAllocTimes h
            b = case compare a x of
                    GT -> y + nf
                    _ -> y
            nf = length . hLookup h . head . hAddresses $ h
            h = heap state

timFinal :: TimState -> Bool
timFinal = null . currentCode 

advance :: TimState -> TimState
advance state = case ins of
    Take n ->   let (newHeap, fptr) = fAlloc oHeap clss
                    (clss, stack') = splitAt n oStack
                in setStack stack' . setFramePtr fptr . setHeap newHeap $ 
                    newState
    Push a ->   let cls = timAddr2Cls a state
                in setStack (cls : oStack) newState
    Enter a ->  let (c, fptr) = timAddr2Cls a state
                in setCurrentCode c $ setFramePtr fptr state
    where   ins : code = currentCode state
            oFramePtr = framePtr state
            oStack = stack state
            oHeap = heap state
            oCodeStore = codeStore state
            newState = setCurrentCode code state

timAddr2Cls :: TimAddr -> TimState -> Closure
timAddr2Cls addr state = case addr of
    Arg k -> fGet oHeap oFramePtr k
    Labal x -> 
        (aLookup oCodeStore x (defErr x), oFramePtr)
    Code c -> (c, oFramePtr)
    IntConst n -> (intCode, FrameInt n)
    where   oHeap = heap state
            oFramePtr = framePtr state
            oCodeStore = codeStore state

intCode :: [Instruction]
intCode = []

-- TODO: add garbage collector, following every frame ptr needed 
--  in each closure to find out all living frames in heap

------------------------------------------------------------------------------

-- | formatting output
showResult :: [TimState] -> String
showResult states = cToStr $ cIntercalate cNewline 
    [showCodeStore . codeStore . head $ states, 
        showState (last states), 
        showStats . stats . last $ states]

-- | formatting full output
showFullResult :: [TimState] -> String
showFullResult states = cToStr $ cIntercalate cNewline
    [showCodeStore . codeStore . head $ states, 
        cIntercalate spt $ map showState states, 
        showStats . stats . last $ states]
    where spt = cConcat [cNewline, cStr "----", cNewline]

showCodeStore :: TimCodeStore -> Cseq
showCodeStore = cIntercalate cNewline . map showSc . aToList

showSc :: (Name, [Instruction]) -> Cseq
showSc (name, ins) = cConcat [cStr name, cStr ": ", showCode Full ins]

-- This data type controls the form of TimAddr when printing instructions
data Form = Full | Laconic | Short

showCode :: Form -> [Instruction] -> Cseq
showCode form code = case form of
    Full -> cIntercalate (cStr ", ") . map (showInstruction Full) $ code
    Laconic -> cIntercalate (cStr ", ") . map (showInstruction Short) $ code
    Short -> cStr "..."

showInstruction :: Form -> Instruction -> Cseq
showInstruction form ins = case ins of
    Take n -> cStr "Take " `cAppend` cNum n
    Push ta -> cStr "Push " `cAppend` showTimAddr form ta
    Enter ta -> cStr "Enter " `cAppend` showTimAddr form ta

showTimAddr :: Form -> TimAddr -> Cseq
showTimAddr form ta = case ta of
    Arg n -> cStr "Arg " `cAppend` cNum n
    Labal s -> cStr "Label " `cAppend` cStr s
    IntConst n -> cStr "Number " `cAppend` cNum n
    Code c ->   let cc = showCode form c
                in cStr "Code [" `cAppend` cc `cAppend` cStr "]"

showStats :: TimStats -> Cseq
showStats s = cConcat [cStr "Statistics: ", cNewline, cStr (space 4),
    cIndent $ cConcat [cStr "Total Steps: ", cNum (step s), cNewline,
    cStr "MaxStepDepth: ", cNum (maxStackDepth s), cNewline,
    cStr "Heap allocation of ", cNum x, cStr " frames and ", cNum y,
    cStr " closures.", cNewline,
    cStr "Execution times: ", cNum (execTime s)]]
    where (x, y) = heapLog s

showState ::TimState -> Cseq
showState = cIntercalate cNewline . 
    (<*>) [showCurrentCode, 
        \s -> showFramePointer (heap s) (framePtr s),
        showStack, 
        showValueStack, 
        showDump] . 
    pure

showCurrentCode :: TimState -> Cseq
showCurrentCode state = cConcat [cStr "Current Code: ", cNewline, 
    cStr "  ", showCode Laconic $ currentCode state]

showFramePointer :: TimHeap -> FramePtr -> Cseq
showFramePointer h ptr = 
    let cptr = case ptr of
            FrameAddr addr -> cStr "Frame Address: " `cAppend` cNum addr
            FrameInt n -> cStr "Number " `cAppend` cNum n
            FrameNull -> cStr "Null Pointer"
    in cStr "Frame Pointer -> " `cAppend` cptr

showStack :: TimState -> Cseq
showStack state = cConcat [cStr "Stack: ", cNewline,
    cStr "  ", cIndent (cIntercalate cNewline $ map (showClosure h) s) ]
        where TimState _ _ s _ _ h _ _ = state

showClosure :: TimHeap -> Closure -> Cseq
showClosure h (code, fptr) = cConcat [
    cStr "code: ", showCode Laconic code, cNewline,
    cStr "frame: ", showFramePointer h fptr]

showValueStack :: TimState -> Cseq
showValueStack state = cConcat [cStr "ValueStack: "]

showDump :: TimState -> Cseq
showDump state = cConcat [cStr "Dump: "]
