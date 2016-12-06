--Module Base(

--    ) where

import Data.List (intercalate)

-- | Expressions are the basic unit of the /Core Language/
-- and thus a new data type is defined. Expression can be variable,
-- number, type constructor, function application, let binding,
-- case expression and lambda abstraction, and limited to these things.
-- | The type parameter is the data type of binders,
-- and at most of the time it will be name, the only exception occurs while
-- dealing with lambda lifting in Chapter 6 of the book. 
data Expr a = EVar Name
                -- ^ variable
            | ENum Int
                -- ^ number
            | EConstr Int Int
                -- ^ constructor
            | EAp (Expr a) (Expr a)
                -- ^ function application
            | ELet
                IsRec
                    -- ^ flag of recursion
                [(a,Expr a)]
                    -- ^ definations
                (Expr a)
                    -- ^ body of let
            | ECase
                (Expr a)
                    -- ^ expression to be scrutinised
                [Alter a]
                    -- ^ alternatives
            | ELam [a] (Expr a)
                    -- ^ lambda expression
            deriving (Show)
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

-- | The flag to determine whether the let binding is recursive or not,
-- -- and the two boolen values are defined as follows:
type IsRec = Bool
recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

-- | Extract the binders from definations in let binding
bindersOf :: [(a,b)] -> [a]
bindersOf = map fst

-- | Extract the right-hand sides of the binding
rhssOf :: [(a,b)] -> [b]
rhssOf = map snd

--------------------------------------------------------


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

---------------------------------------------------------

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

data Cseq   = CTip
            | CStr String
            | CAppend Cseq Cseq

-- | empty container
cEmpty :: Cseq
cEmpty = CTip

-- | put a string in the container
cStr :: String -> Cseq
cStr str = CStr str

-- | put a connection request in a container
cAppend :: Cseq -> Cseq -> Cseq
CTip `cAppend` cseq = cseq
cseq `cAppend` CTip = cseq
cseq1 `cAppend` cseq2 = CAppend cseq1 cseq2

-- | concatenate a list of cseqs to one
cConcat :: [Cseq] -> Cseq
cConcat = foldr cAppend CTip

-- | @intercalate@ for Cseq
cIntercalate :: Cseq -> [Cseq] -> Cseq
cIntercalate cspt = foldr1 
    (\x y -> x `cAppend` cspt `cAppend` y)

-- | expand the cseq container to a string
cExpand :: [Cseq] -> String
cExpand [] = []
cExpand (CTip : as) = cExpand as
cExpand (CStr a : as) = a ++ cExpand as
cExpand (CAppend a b : as) = cExpand (a:b:as)

-- | turn a program into cseq
pprProgram :: CoreProgram -> Cseq
pprProgram = cConcat . map pprScDef
    where pprScDef (var,vars,expr) =
            cStr var `cAppend` 
            cStr (' ':unwords vars) `cAppend`
            CStr " = " `cAppend`
            pprExpr expr `cAppend`
            CStr "\n"

-- | turn expression into cseq, use pattern match to deal with different values.
pprExpr :: CoreExpr -> Cseq
pprExpr (EVar var) = cStr var
pprExpr (ENum num) = cStr.show $ num
pprExpr (EConstr tag arity) =
    CStr "Pack{" `cAppend` (cStr.show $ tag) `cAppend`
    CStr "," `cAppend` (cStr.show $ arity) `cAppend` CStr "}"
pprExpr (EAp func x) = pprExpr func `cAppend` CStr " " `cAppend` pprAExpr x
--pprExpr (ELet flag varExpr bodyExpr) =
--    "let " `cAppend` 
--    (intercalate " ; " $ map (\(v,e) -> v`cAppend`" = "`cAppend`pprExpr e) varExpr) `cAppend`
--     "in " `cAppend` pprExpr bodyExpr
--pprExpr (ECase expr alts) =
--    "case "`cAppend`pprExpr expr`cAppend`" of \n\t"`cAppend`
--    intercalate "\n\t" (map (\(tag,vars,altExpr) -> 
--        "<"`cAppend`show tag`cAppend`"> "`cAppend`
--        (intercalate " " vars)`cAppend`" -> "`cAppend`
--        pprExpr altExpr) alts)
--pprExpr (ELam vars expr) = "(\\ "`cAppend`unwords vars`cAppend` " . " `cAppend` pprExpr expr `cAppend` ")"

-- parenthese non-atomic expression
pprAExpr :: CoreExpr -> Cseq
pprAExpr e
    | isAtomicExpr e = pprExpr e
    | otherwise = CStr "(" `cAppend` pprExpr e `cAppend` CStr ")"


