-----------------------------------------------------------------------------
-- |
-- Module:  CoreLanguage.Base
--
-- The basic module of /Core Language/, including three parts
--
--  * basic data types
--  * a simple prelude
--  * a code printer
--
-----------------------------------------------------------------------------

module Base (

    -- * Data types
    Expr(..), Alter(..), ScDef(..), Program(..), Cseq(..)
    , CoreExpr, CoreAlter, CoreScDef, CoreProgram
    , Name, IsRec

    -- * prelude functions and some basic auxilary functions
    , preludeDefs
    , isAtomicExpr, bindersOf, rhssOf, recursive, nonRecursive

    -- * Code Printer
    , pPrint

    -- ** String Container

    -- *** basic element
    , cEmpty, cStr, cNum
   
     -- *** format control
    , cNewline, cIndent
    
    -- *** combination
    , cAppend, cConcat, cIntercalate
    
    -- *** table
    , cLPNum, cNumList
    
    -- *** transform back to string
    , cToStr
    
    )where

import Utility

-- | Expressions are the basic unit of the /Core Language/
-- and thus a new data type is defined. Expression can be variable,
-- number, type constructor, function application, let binding,
-- case expression and lambda abstraction, and limited to these things.
-- 
-- The type parameter is the data type of binders, and at most of the time 
-- it will be name, the only exception occurs while dealing with 
-- lambda lifting in Chapter 6 of the book. 
data Expr a = EVar Name
                -- ^ variable
            | ENum Int
                -- ^ number
            | EConstr Int Int
                -- ^ constructor
            | EAp (Expr a) (Expr a)
                -- ^ function application
            | ELet IsRec [(a,Expr a)] (Expr a)
                -- ^ let bindings with a flag indicating it being recursive
            | ECase (Expr a) [Alter a]
                -- ^ expression to be scrutinised and alternatives
            | ELam [a] (Expr a)
                -- ^ lambda expression
            deriving (Eq, Show)
type CoreExpr = Expr Name

-- type synonymas are used to define the type of coreExpr
-- and the following parameterized auxiliary data types.

-- | Variable names are just strings.
type Name = String

-- | Alternatives of case expression
-- including tag, list of vars and the expression to the right of the arrow.
type Alter a = (Int,[a],Expr a)
type CoreAlter = Alter Name

-- | Programs are build up by supercombinator definations.
type Program a = [ScDef a]
type CoreProgram = Program Name

-- | A supercombinator definition contains the name of the supercombinator, 
-- its arguments and its body.
type ScDef a = (Name,[a],Expr a)
type CoreScDef = ScDef Name

-- The followings are some auxiliary functions

-- | Is it an atomic expression?
isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False

-- | The flag to determine whether the let binding is recursive or not
type IsRec = Bool
-- | Rename bool value to make it more comprehensive
recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

-- | Extract the binders from definations in let binding
bindersOf :: [(a,b)] -> [a]
bindersOf = map fst

-- | Extract the right-hand sides of the binding
rhssOf :: [(a,b)] -> [b]
rhssOf = map snd

-----------------------------------------------------------------------------


-- | A rather small prelude including six functions:
--
-- > id x = x
-- > k1 x y = x
-- > k2 x y = y
-- > S f g x = f x (g x)
-- > compose f g x = f (g x)
-- > twice f = compose f f
-- 
-- It is hoped to work for all implementations,
-- so it just include the simplest, pre-defined implementation: 
-- function application. 
preludeDefs :: CoreProgram
preludeDefs = [ ("id",["x"],EVar "x"),
                ("k1",["x","y"],EVar "x"),
                ("k2",["x","y"],EVar "y"),
                ("S",["f","g","x"],
                    EAp (EAp (EVar "f") (EVar "x")) 
                        (EAp (EVar "g") (EVar "x"))),
                ("compose",["f","g","x"],
                    EAp (EVar "f") (EAp (EVar "g") (EVar "x"))),
                ("twice",["f"],
                    EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))]

-----------------------------------------------------------------------------

-- | First define a data type for printing code effectively.
--
-- Because simply using @++@ to connect string will lead to
-- unexpected quadratic time complexity, comes from the fact
-- that @++@ will tranverse its first operand.
--
-- Although there's the lazy evaluation feature, doing @(a++b)++c@ 
-- still needs more reduction steps than that of @a++(b++c)@.
-- The basic idea is to keep the string connecting as part of
-- this new data type and keep it unevaluated until we need to print it out.
-- The new data type acts just like a container.

data Cseq   = CNil
            | CStr String
            | CAppend Cseq Cseq
            | CNewline
            | CIndent Cseq

-- | empty container
cEmpty :: Cseq
cEmpty = CNil

-- | put a string in the container, and subsititute line break
-- to @cNewLine@
cStr :: String -> Cseq
cStr "" = CNil
cStr s = cIntercalate cNewline .  map CStr . lines $ s

-- | put a connection request in a container
cAppend :: Cseq -> Cseq -> Cseq
CNil `cAppend` cseq = cseq
cseq `cAppend` CNil = cseq
cseq1 `cAppend` cseq2 = CAppend cseq1 cseq2

-- | put a line break with indentation in container
cNewline :: Cseq
cNewline = CNewline

-- | put an indentation indication in container
cIndent :: Cseq -> Cseq
cIndent = CIndent

-- | concatenate a list of cseqs to one
cConcat :: [Cseq] -> Cseq
cConcat = foldr cAppend CNil

-- | @intercalate@ for Cseq
cIntercalate :: Cseq -> [Cseq] -> Cseq
cIntercalate _ [] = CNil
cIntercalate cspt cs = foldr1 (\x y -> x `cAppend` cspt `cAppend` y) cs

-- | put a number in container
cNum :: Int -> Cseq
cNum = cStr.show

-- | left padding number form, @cLPNum pd num@ make sure the string of @num@
-- occupying @pd@ width of space
cLPNum :: Int -> Int -> Cseq
cLPNum pd num = cStr (space (pd - length ns))
                    `cAppend` cStr ns
    where ns = show num

-- | numbered list
cNumList :: [Cseq] -> Cseq
cNumList = cConcat . zipWith lst [1..]
    where lst sn cseq = cConcat [ cLPNum 4 sn, cStr ") ", cIndent cseq, cNewline ]

-- | expand the cseq container to a string
cToStr :: Cseq -> String
cToStr cseq = cExpand 0 [(cseq,0)]

-- | auxiliary function of cToStr
cExpand :: Int          -- keep track of current column 
        -> [(Cseq,Int)] -- the int indicates indentation 
        -> String
cExpand _ [] = []
cExpand col ((CNil, _) : as) = cExpand col as
cExpand col ((CStr a, _) : as) = a ++ cExpand (col+length a) as
cExpand col ((CAppend a b, ind) : as) = cExpand col ((a,ind):(b,ind):as)
cExpand col ((CNewline, ind) : as) = 
    '\n':space ind ++ cExpand ind as
cExpand col ((CIndent a, ind) : as) = cExpand col ((a,col) : as)

-----------------------------------------------------------------------------

-- | print the program code
pPrint :: CoreProgram -> String
pPrint = cToStr.pprProgram 

-- | turn a program into cseq
pprProgram :: CoreProgram -> Cseq
pprProgram = cIntercalate spt . map pprScDef
    where spt = cStr ";" `cAppend` cNewline

pprScDef :: CoreScDef -> Cseq
pprScDef (var,vars,expr) =
    cConcat [   cStr var, cStr (' ':unwords vars),
                cStr misc, cIndent (pprExpr expr) ]
    where misc  | null vars = "= " | otherwise = " = "

-- | turn expression into cseq, use pattern match to deal with different constructors.
-- 
-- When dealing with function application, certain operators will take the infix form
-- and parenthesised according to precedence, show as below:
--
--  * Precedence    Operator
--  *       6       Application
--  *       5       *,/
--  *       4       +,-
--  *       3       ==,~=,>,>=,<,<=
--  *       2       &
--  *       1       |
pprExpr :: CoreExpr -> Cseq
pprExpr (EVar var) = cStr var
pprExpr (ENum num) = cStr.show $ num
pprExpr (EConstr tag arity) =
    cStr "Pack{" `cAppend` (cStr.show $ tag) `cAppend`
    cStr ", " `cAppend` (cStr.show $ arity) `cAppend` cStr "}"
pprExpr (EAp func x) = pprFAExpr 0 (EAp func x)
pprExpr (ELet isRec varExpr bodyExpr) =
    cConcat [   cStr keyword, cNewline,
                cStr "    ", cIndent (pprDefs varExpr), cNewline,
                cStr "in ", pprExpr bodyExpr ]
    where keyword
            | isRec = "letrec"
            | otherwise = "let"
pprExpr (ECase expr alts) =
    cConcat [   cStr "case ", pprExpr expr, cStr " of ", cNewline,
                cStr "    ", cIndent (pprAlts alts) ]
pprExpr (ELam vars expr) = 
    cConcat [ cStr "\\ ", cStr (unwords vars), cStr " -> ", pprExpr expr ]

-- pcd is upper level operator precedence.
pprFAExpr :: Int -> CoreExpr -> Cseq
pprFAExpr pcd (EAp (EAp (EVar op) x) y)
-- infix binary operator cases
    | opPcd < 6 && opPcd <= pcd = cConcat [ cStr "(", pprFAExpr opPcd x, 
                                            cStr " ", cStr op, cStr " ",
                                            pprFAExpr opPcd y, cStr ")" ]
    | opPcd < 6 = cConcat [ pprFAExpr opPcd x, cStr " ", cStr op,
                            cStr " ", pprFAExpr opPcd y ]
-- general operator cases
    | pcd == 6 = cConcat [  cStr "(", cStr op, cStr " ", pprFAExpr opPcd x,
                            cStr " ", pprFAExpr opPcd y, cStr ")" ]
    | otherwise = cConcat [ cStr op, cStr " ", pprFAExpr opPcd x, 
                            cStr " ", pprFAExpr opPcd y ]
        where opPcd
                | op `elem` ["*","/"] = 5
                | op `elem` ["+","-"] = 4
                | op `elem` ["==","/=",">",">=","<","<="] = 3
                | op == "&" = 2
                | op == "|" = 1
                | otherwise = 6
-- more general function application cases
pprFAExpr pcd (EAp func x)
    | pcd == 6 = cConcat [  cStr "(", pprFAExpr 5 func, cStr " ",
                            pprFAExpr 6 x, cStr ")" ]
    | otherwise = cConcat [ pprFAExpr 5 func, cStr " ", pprFAExpr 6 x ]
-- other expression return to normal pprExpr
pprFAExpr _ expr = pprExpr expr

-- auxiliary function to print definations in let binding
pprDefs :: [(Name,Expr Name)] -> Cseq
pprDefs = cIntercalate spt . map pprDef
    where spt = cStr ";" `cAppend` cNewline

pprDef :: (Name,Expr Name) -> Cseq
pprDef (var,expr) = cConcat [   cStr var, cStr " = ",
                                cIndent (pprExpr expr) ]

-- auxiliary function to print alternatives in case expression
pprAlts :: [CoreAlter] -> Cseq
pprAlts = cIntercalate spt . map pprAlt
    where spt = cStr ";" `cAppend` cNewline

pprAlt :: CoreAlter -> Cseq
pprAlt (tag,vars,expr) = 
    cConcat [   cStr "<", cStr (show tag), cStr "> ",
                cStr (unwords vars), cStr " -> ",
                cIndent (pprExpr expr) ]

