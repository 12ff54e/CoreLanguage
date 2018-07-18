------------------------------------------------------------------------------
--
-- | 
-- Module   : CoreLanguage.GMachine
--
-- A graph reducer based on g-machine, which complies all supercombinators to
-- instructions (equivalently, postfix expressions) before evaluation.
--
------------------------------------------------------------------------------


module GMachine (

    -- * run the program
    run

    ) where

import Base
import Parser
import Utility

-- | the state used in g-machine
type GmState = (GmCode, GmStack, GmDump, GmHeap, GmGlobals, GmStats)
-- TODO: Implements Print instruction & add output in state

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
--  * @Pack tag arity@ takes @arity@ of the stack to construct
--      a constructor node
--  * @Split n@ decompose a construtor(located on the top of stack) into
--      its parameters
--  * @CaseJump caselist@ pick the code pieces in @caselist@ according to
--      the constructor on top of stack
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
                    | Pack Int Int
                    | Split Int
                    | CaseJump [(Int, GmCode)]
                    | Neg | Add | Sub | Mul | Div
                    | Eq | Neq | Lt | Gt | Leq | Geq
                    | Null
                    | MakeGlobal Int GmCode
    deriving (Eq, Show)

getCode :: GmState -> GmCode
getCode (c,_,_,_,_,_) = c

putCode :: GmCode -> GmState -> GmState
putCode c' (_, sk, d, h, g, ss) = (c', sk, d, h, g, ss)

type GmStack = [Addr]

getStack :: GmState -> GmStack
getStack (_,s,_,_,_,_) = s

putStack :: GmStack -> GmState -> GmState
putStack sk' (c, _, d, h, g, ss) = (c, sk', d, h, g, ss)

type GmDump = [(GmCode, GmStack)]

getDump :: GmState -> GmDump
getDump (_,_,d,_,_,_) = d

putDump :: GmDump -> GmState -> GmState
putDump d' (c, sk, _, h, g, ss) = (c, sk, d', h, g, ss)

type GmHeap = Heap Node

getHeap :: GmState -> GmHeap
getHeap (_,_,_,h,_,_) = h

putHeap :: GmHeap -> GmState -> GmState
putHeap h' (c, sk, d, _, g, ss) = (c, sk, d, h', g, ss)

-- | the supercombinator node now stores numbers of arguments taken and
-- instructions, differs from that in tempelate instantiation machine
data Node   = NAp Addr Addr
            | NNum Int
            | NGlobal Int GmCode
            | NInd Int
            | NConstr Int [Addr]

type GmGlobals = Assocs Name Addr

getGlobals :: GmState -> GmGlobals
getGlobals (_,_,_,_,g,_) = g

putGlobals :: GmGlobals -> GmState -> GmState
putGlobals g' (c, sk, d, h, _, ss) = (c, sk, d, h, g', ss)

data GmStats = GmStep   { step :: Int
                         ,maxStk :: Int
                         ,maxDmp :: Int
                        }

gmStatsInit :: GmStats
gmStatsInit = GmStep 0 0 0

gmStatsIncStep :: GmStats -> GmStats
gmStatsIncStep (GmStep n x y) = GmStep (n+1) x y

gmStatsChangeMaxStk :: Int -> GmStats -> GmStats
gmStatsChangeMaxStk n' (GmStep x _ y) = GmStep x n' y

gmStatsChangeMaxDmp :: Int -> GmStats -> GmStats
gmStatsChangeMaxDmp n' (GmStep x y _) = GmStep x y n'

getStats :: GmState -> GmStats
getStats (_,_,_,_,_,ss) = ss

putStats :: GmStats -> GmState -> GmState
putStats ss' (c, sk, d, h, g, _) = (c, sk, d, h, g, ss')

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
    EConstr tag arity -> 
        [PushGlobal ("Pack{"++show tag++","++show arity++"}")]
    ECase _ _ -> error "can't compile case expression in lazy scheme yet" -- FIXME: remove this error
--    ECase body alters -> take nargs [Push n | n <- [depth ..]] ++
--        [MakeGlobal nargs (compileExprStrict 0 args expr)] ++
--        replicate nargs Mkap
--            where nargs = length args
    ELam _ _ -> error "can't compile lambda expression yet"

compileExprStrict :: Int -> [Name] -> CoreExpr -> GmCode
compileExprStrict depth args expr =
    case expr of 
        ENum num -> [PushInt num]
        ELet isRec bindings body -> 
            compileLetStrict isRec bindings body depth args
        EConstr tag arity -> [Pack tag arity]
        ECase body alters -> compileExprStrict depth args body ++ 
            [CaseJump (map (compileAlter depth args) alters)]
--        EAp func x -> case func of
--            EVar "negate" -> compileExprStrict depth args x ++ [Neg]
--            EAp (EVar op) y
--                | ins /= Null ->  
--                    compileExprStrict depth args y ++ 
--                    compileExprStrict (depth+1) args x ++
--                    [ins]
--                | otherwise -> defaultCase
--                where ins = aLookup builtinBinOp op Null
--            _ 
--                | apHead func == EConstr tag arity -> undefined                                 
--                | otherwise -> defaultCase
        EAp _ _ -> case last plainExpr of
            EVar "negate"
                | exprLength /= 2 -> 
                    error "negate applied to too many arguements"
                | otherwise -> 
                    compileExprStrict depth args (head plainExpr) ++ [Neg]
            EVar op
                | ins /= Null -> case () of
                    _   | exprLength < 3 -> 
                            error (op++" applied to too few arguements")
                        | exprLength > 3 ->
                            error (op++" applied to too many arguements")
                        | otherwise -> let y:x:_ = plainExpr in
                                        compileExprStrict depth args y ++ 
                                        compileExprStrict (depth+1) args x ++
                                        [ins]
                | otherwise -> defaultCase
                where ins = aLookup builtinBinOp op Null
            EConstr tag arity 
                | exprLength /= arity+1 -> 
                    error "arguement number mismatch"
                | otherwise -> concat 
                    (zipWith (`compileExpr` args) [depth ..] (init plainExpr))
                    ++ [Pack tag arity]
            _ -> defaultCase
            where plainExpr = flatten expr
                  exprLength = length plainExpr
        _ -> defaultCase
        where defaultCase = compileExpr depth args expr ++ [Eval]
              flatten apChain = case apChain of
                                EAp f x -> x : flatten f
                                _ -> [apChain]

compileLet  :: IsRec -> [(Name, CoreExpr)] -> CoreExpr  
            -> Int -> [Name] -> GmCode
compileLet isRec bindings body depth args
    | isRec == nonRecursive = concat (
        zipWith (`compileExpr` args) [depth ..] (reverse defs))
        ++ compileWithDefs body ++ [Slide nDefs]
    | otherwise = [Alloc nDefs] 
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
    | otherwise = [Alloc nDefs] 
        ++ concat (zipWith (++) 
            (map (compileExpr 0 args') defs)
            (map (\n -> [Update n]) [0..(nDefs-1)]))
        ++ cwds body ++ [Slide nDefs]
        where nDefs = length bindings
              defs = rhssOf bindings
              cwds = compileExprStrict 0 args'
              args' = bindersOf bindings ++ replicate depth "_" ++ args

compileAlter :: Int -> [Name] -> CoreAlter -> (Int, GmCode)
compileAlter depth args (tag, constrArgs, body) = (tag, code)
    where code = [Split arity] ++ compileExprStrict 0 args' body ++ 
                    if' (arity==0) [] [Slide arity]
          args' = constrArgs ++ replicate depth "_" ++ args
          arity = length constrArgs

-- | return the index of specific element first appears in a list, 
-- and return -1 if element not in the list
findIndex :: Eq a => a -> [a] -> Int
findIndex e es = go e es
    where go _ [] = - length es - 1
          go x (y:ys)
            | x==y = 0
            | otherwise = 1 + go x ys

compiledPrim :: [(Name, Int, GmCode)]
compiledPrim = 
    ("negate", 1, [Push 0, Eval, Neg, Update 1, Pop 1, Unwind]) : 
--    ("+", 2, [Push 1, Eval, Push 1, Eval, Add, Update 2, Pop 2, Unwind]),
--    ("-", 2, [Push 1, Eval, Push 1, Eval, Sub, Update 2, Pop 2, Unwind]),
--    ("*", 2, [Push 1, Eval, Push 1, Eval, Mul, Update 2, Pop 2, Unwind]),
--    ("/", 2, [Push 1, Eval, Push 1, Eval, Div, Update 2, Pop 2, Unwind]) ]
    [(name, 2, [Push 1, Eval, Push 1, Eval]++op:[Update 2, Pop 2, Unwind]) 
        | (name, op) <- aToList builtinBinOp]

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
                  _ -> False

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
        stack@(a:as) = getStack state
        dump = getDump state
        heap = getHeap state
        newState = putCode code state
    in case ins of
        PushGlobal name -> pushGlobal name newState
        PushInt num -> 
            let (newHeap, addr) = hAlloc heap (NNum num) 
            in putHeap newHeap $ putStack (addr:stack) newState
        Push n ->  putStack ((stack!!n):stack) newState
        Mkap -> let (newHeap, addr) = hAlloc heap (NAp a1 a2)
                    a1:a2:stack' = stack
                    newStack = addr:stack'
                in putStack newStack $ putHeap newHeap newState
        Slide n -> putStack (a : drop n as) newState
        Update n -> putStack as $ 
            putHeap (hUpdate heap (stack !! (n+1)) (NInd a)) newState
        Pop n -> putStack (drop n stack) newState
        Unwind -> unwind newState
        Alloc n -> let (newHeap, aNulls) = mapAccuml hAlloc heap $
                                        replicate n (NInd hNull)
                   in putStack (aNulls++stack) $ putHeap newHeap newState
        Eval -> putCode [Unwind] . putDump ((code,as):dump) . 
                    putStack [a] $ state
        Pack tag arity -> let (newHeap, addr) = 
                                hAlloc heap (NConstr tag (take arity stack))
                          in putHeap newHeap $ putStack (addr:stack) newState
        Split arity
            | length args == arity -> putStack (args++as) newState
            | otherwise -> 
                error "pattern match failed: arguement numbers mismatch"
            where NConstr _ args = hLookup heap (head stack)
        CaseJump alters -> caseJump alters newState
        prims -> primStep prims newState

pushGlobal :: Name -> GmState -> GmState
pushGlobal name state
    | take 4 name == "Pack" = case () of
        _   | addr == hNull -> putGlobals newGlobals . 
                putHeap newHeap . putStack (newAddr:stack) $ state
            | otherwise -> putStack (addr:stack) state
    | otherwise =   let err = error $ "can't find defination of "++name 
                    in putStack (aLookup globals name err : stack) state
        where globals = getGlobals state
              stack = getStack state  
              addr = aLookup globals name hNull
              newGlobals = aInsert (name, newAddr) globals
              (newHeap, newAddr) = 
                hAlloc (getHeap state) (NGlobal arity code)
              (EConstr tag arity, _) = head . pExpr . clex (0,0) $ name
              code = [Pack tag arity, Slide arity, Unwind]

caseJump :: [(Int, GmCode)] -> GmState -> GmState
caseJump alters state = putCode (alter ++ getCode state) state
    where alter = go alters tag
          NConstr tag _ = hLookup (getHeap state) . head . getStack $ state
          go ((t,c):as) x
            | t==x = c
            | otherwise = go as x
          go [] _ = error "case has no alternatives" 

unwind :: GmState -> GmState
unwind state = case hLookup (getHeap state) addr of
    NNum _ -> checkDump
    NAp a1 _ -> putCode [Unwind] $ putStack (a1:stack) state
    NGlobal n code
        | length stack < n -> error "not enough arguments"
        | otherwise -> putCode code $ rearrange n state
    NInd aInd -> putCode [Unwind] $ putStack (aInd:as) state
    NConstr _ _ -> checkDump
    where stack@(addr:as) = getStack state
          checkDump = case getDump state of
            (c,s):ds -> putDump ds . putCode c . putStack (addr:s) $ state
            _ -> state

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

boxBool :: Bool -> GmState -> GmState
boxBool b state = putStack (addr: getStack state) $ putHeap newHeap state
    where (newHeap, addr) = hAlloc (getHeap state) (NConstr b' [])
          b' | b = 1 | otherwise = 2

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

primCompare :: (Int -> Int -> Bool) -> GmState -> GmState
primCompare = primBinary boxBool unboxInteger

primStep :: Instruction -> GmState -> GmState
primStep prim = case prim of
    Neg -> primArith1 negate
    Add -> primArith2 (+)
    Sub -> primArith2 (-)
    Mul -> primArith2 (*)
    Div -> primArith2 div
    Lt -> primCompare (<)
    Gt -> primCompare (>)
    Eq -> primCompare (==)
    Neq -> primCompare (/=)
    Leq -> primCompare (<=)
    Geq -> primCompare (>=)
    _ -> error "Just in case"

------------------------------------------------------------------------------

-- | formatting the output
showResult :: [GmState] -> String
showResult [] = error "Just in case"
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
pprCode = cIntercalate (cStr " ,") . map pprInstruction

pprInstruction :: Instruction -> Cseq
pprInstruction = cStr . show

pprState :: GmState -> Cseq
pprState (code, stack, _, heap, globals, _) = cConcat [   
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
        NInd aInd -> cStr "Indirection to " `cAppend` cNum aInd
        NConstr tag args -> cIntercalate (cStr " ") 
            [cStr "Constr", cNum tag, cStr (show args)]
    ]

pprStatistics :: GmState -> Cseq 
pprStatistics state = cStr "  " `cAppend` cIndent (cConcat [   
    cStr "Steps taken is ", cNum $ step stats, cNewline,
    cStr "Max Stack Depth is ", cNum $ maxStk stats, cNewline,
    cStr "Max Dump Depth is ", cNum $ maxDmp stats ])
    where stats = getStats state

