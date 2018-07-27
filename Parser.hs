-----------------------------------------------------------------------------
-- |
-- Module:  CoreLanguage.Parser
--
-- This module provide a parser for /Core Language/, transform primitive
-- code string into syntax forest represented by data type defined in 
-- @CoreLanguage.Base@ module.
--
-----------------------------------------------------------------------------

module Parser (
    -- * parser
    parse

    -- * auxiliaries

    -- ** data types
    , Token, Parser

    -- ** lexical 
    , clex

    -- ** syntactic
    , pExpr, pScDef
    , syntax

    )where

import Base

-- | A parser is composition of clexical analyser
-- and syntax analyser.
parse :: String -> CoreProgram
parse = syntax . clex (0,0)

clex :: (Int,Int) -> String -> [Token]

-- | tokens with its line and column number
type Token = ((Int,Int),String)

-- | parser take a list of tokens and return 
-- all possibles of "word" it recognized, 
-- paired with remaining list of tokens.
type Parser a = [Token] -> [(a,[Token])]

-----------------------------------------------------------------------------

-- | The lexical analyser breaks the input string
-- into token list, it should:
--
--  * omits whitespace characters and comments,
--      introduced by double hyphen and extends to
--      the end of the line
--  * recognize digits cluster as number
--  * recognize variable names, starting by letter
--      and consist only letters, digits and underscore
--  * recognize two character operators, e.g. "=="
--  * record the line and column number of each token
clex _ [] = []
clex (row,col) (c:cs)
    | c == '\n' = clex (row+1,0) cs
    | isWhitespace c = clex (row,col+1) cs
    | isComment ch2 = clex (row+1,0) cRes
    | isDigit c = ((row,col),c:num_t) : clex (row,1+col+length num_t) nRes
    | isLetter c = ((row,col),c:var_t) : clex (row,1+col+length var_t) vRes
    | isTwoCharOp ch2 = ((row,col),ch2) : clex (row,2+col) oRes
    | otherwise = ((row,col),[c]) : clex (row,1+col) cs
        where   ch2 = [c,head cs]
                cRes = dropWhile (/= '\n') cs
                (num_t,nRes) = span isDigit cs
                (var_t,vRes) = span isVarChar cs
                oRes = tail cs

-- | functions judging whether a char belongs to specific field
isWhitespace, isDigit, isLetter, isVarChar :: Char -> Bool
isWhitespace = (`elem` " \t\n")
isDigit = (`elem` ['0'..'9'])
isLetter = (`elem` ['a'..'z']++['A'..'Z'])
isVarChar c = isLetter c || isDigit c || c == '_'

isTwoCharOp, isComment :: String -> Bool
isTwoCharOp = (`elem` ["==","<=",">=","/=","->"])
isComment = (== "--")

---------------------------------------------------------
-- Auxiliary functions for syntax analyser

-- Reserved words and symbols
keywords :: [String]
keywords = ["let","letrec","in","case","of","Pack"]

-- infix operator with precedence from 1 to 5, and
-- function application has precedence 6
operators :: [[String]]
operators = [   [ "|" ],
                [ "&" ],
                [ "==", "/=", "<", "<=", ">", ">=" ],
                [ "+", "-" ],
                [ "*", "/" ] ]

-- | construct a parser that take the first token if
-- it satisfied the predict, and return empty list if failed
pSat :: (Token -> Bool) -> Parser String
pSat prd [] = []
pSat prd (tok:toks)
    | prd tok = [(snd tok, toks)]
    | otherwise = []

-- | parse the first token if it's the same as the string given
pLit :: String -> Parser String
pLit str = pSat (\(_,t) -> str==t)

-- | construct a parser equivalent to apply the function to the origin
-- parser's result
pApply :: Parser a -> (a->b) -> Parser b
pApply p f toks = [ (f x,toks') | (x,toks') <- p toks ]

-- | a parser for variables 
pVar :: Parser Name 
pVar = pSat (\(_,tok) -> 
    (isLetter.head) tok && notElem tok keywords)

-- | a parser for operators
pOp :: Parser CoreExpr 
pOp = pSat (\(_,tok) -> tok `elem` concat operators) `pApply` EVar

-- | a parser for number
pNum :: Parser Int
pNum = pSat (\(_,tok) -> isDigit $ head tok) `pApply` 
        \ num -> read num :: Int

-- | combine two parser p1 and p2 to contruct a "p1 or p2" parser
pOr :: Parser a -> Parser a -> Parser a
pOr p1 p2 toks = p1 toks ++ p2 toks

-- | contruct a parser always succeed and return the default value,
-- paired with the origin token list
pEmpty :: a -> Parser a
pEmpty def toks = [(def,toks)]

-- | construct a parser equivalent to successively parse the input with 
-- two parsers and combine the value with a function
pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen f p1 p2 toks = [ (f v1 v2, toks2) |   (v1, toks1) <- p1 toks, 
                                            (v2, toks2) <- p2 toks1 ]

-- | extend pThen to accept three parsers
pThen3  :: (a -> b -> c -> d) 
        -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 f p1 p2 p3 toks = 
    [ (f v1 v2 v3, toks3) | (v1, toks1) <- p1 toks,
                            (v2, toks2) <- p2 toks1,
                            (v3, toks3) <- p3 toks2 ]

-- | extend pThen to accept four parsers
pThen4  :: (a -> b -> c -> d -> e) 
        -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
pThen4 f p1 p2 p3 p4 toks = 
    [ (f v1 v2 v3 v4, toks4) |  (v1, toks1) <- p1 toks,
                                (v2, toks2) <- p2 toks1,
                                (v3, toks3) <- p3 toks2,
                                (v4, toks4) <- p4 toks3 ]

-- | parse zero or more parses given by the parser
pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = pOneOrMore p `pOr` pEmpty []

-- | parse one or more parses given by the parser
pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p toks = [ (x:y,toks2) | (x, toks1) <- p toks,  
                                    (y, toks2) <- pZeroOrMore p toks1 ]
 
-- | parse one or more parses with separator given by the two parsers
pOneOrMoreWithSpt :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSpt pct pspt toks = 
    [ (x:y,toks2) | (x, toks1) <- pct toks,
                    (y, toks2) <- pZeroOrMore (pThen ts pspt pct) toks1 ]
        where ts a b = b

-- The alternative version of the corresponding function, return only
--  the longest match.
pZeroOrMore' p toks = [head $ pZeroOrMore p toks]
pOneOrMore' p toks
    | null ps = []
    | otherwise = [head ps]
        where ps = pOneOrMore p toks
pOneOrMoreWithSpt' p1 p2 toks
    | null ps = []
    | otherwise = [head ps]
        where ps = pOneOrMoreWithSpt p1 p2 toks

---------------------------------------------------------------------------
-- Use tool functions to build the /Core Language/ parser

-- | The wrapper function @syntax@, takes the first complete parse,
-- and throw an error message if there's no complete parse.
syntax :: [Token] -> CoreProgram
syntax = tf . pProgram
    where   tf [] = error "syntax error"
            tf ((prog,[]):ps) = prog
            tf (parse:ps) = tf ps

pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSpt pScDef (pLit ";")

pScDef :: Parser CoreScDef
pScDef = pThen4 mk_sc pVar (pZeroOrMore pVar) (pLit "=") pExpr
    where mk_sc binder para equal expr = (binder,para,expr)

-- | expression parser of different data constructor
pExpr, pLet, pCase, pLambda :: Parser CoreExpr
-- | dealing with precedence of build-in binary opertors
pExpr_p1, pExpr_p2, pExpr_p3, pExpr_p4, pExpr_p5, pAExpr :: Parser CoreExpr

pExpr = pLet `pOr` pCase `pOr` pLambda `pOr` pExpr_p1

pLet = pThen4 mk_let (pLit "let" `pOr` pLit "letrec") pDefs (pLit "in") pExpr
    where mk_let kw defs _ = ELet (kw == "letrec") defs 

pCase = pThen4 mk_case (pLit "case") pExpr (pLit "of") pAlts
    where mk_case _ expr _ = ECase expr

pLambda = pThen4 mk_lambda (pLit "\\") (pOneOrMore pVar) (pLit "->") pExpr
    where mk_lambda _ vars _ = ELam vars

-- support parsers of components in expression
pDefs :: Parser [(Name,CoreExpr)]
pDefs = pOneOrMoreWithSpt pDef (pLit ";")
    where pDef = pThen3 mk_def pVar (pLit "=") pExpr
          mk_def var _ expr = (var,expr)

pAlts :: Parser [CoreAlter]
pAlts = pOneOrMoreWithSpt pAlt (pLit ";")
    where   pAlt = pThen4 
                    mk_alt  (pThen3 ts (pLit "<") pNum (pLit ">")) 
                            (pZeroOrMore pVar)
                            (pLit "->") 
                            pExpr
            mk_alt tag vars _ expr = (tag,vars,expr)
            ts _ x _ = x

-----------------------------------------------------------------------------
-- this block dealing with function aplication, infix operator 
-- precedence and assocaitivity

-- In order to improve efficiency in parsing infix operator with precedence, 
-- partial expression data type is introduced.
data PartExpr = NoOp | FoundOp Name CoreExpr

combineOp :: CoreExpr -> PartExpr -> CoreExpr
combineOp expr NoOp = expr
combineOp expr (FoundOp op expr1) = EAp (EAp (EVar op) expr) expr1

pExpr_p1 = pThen combineOp pExpr_p2 pExpr_p1r
pExpr_p2 = pThen combineOp pExpr_p3 pExpr_p2r
pExpr_p3 = pThen combineOp pExpr_p4 pExpr_p3r
pExpr_p4 = pThen combineOp pExpr_p5 pExpr_p4r
pExpr_p5 = pThen combineOp pExpr_p6 pExpr_p5r
pExpr_p6 = pOneOrMore pAExpr `pApply` mk_app_chain
    where mk_app_chain = foldl1 EAp 

pExpr_p1r, pExpr_p2r, pExpr_p3r, pExpr_p4r, pExpr_p5r :: Parser PartExpr
pExpr_p1r = pThen FoundOp (pLit "|") pExpr_p1 `pOr` pEmpty NoOp
pExpr_p2r = pThen FoundOp (pLit "&") pExpr_p2 `pOr` pEmpty NoOp
pExpr_p3r = pThen FoundOp (pSat (\(_,t) -> t `elem` (operators!!2))) pExpr_p4
    `pOr` pEmpty NoOp
pExpr_p4r = pThen FoundOp (pLit "+") pExpr_p4
    `pOr` pThen FoundOp (pLit "-") pExpr_p5 `pOr` pEmpty NoOp
pExpr_p5r = pThen FoundOp (pLit "*") pExpr_p5
    `pOr` pThen FoundOp (pLit "/") pExpr_p6 `pOr` pEmpty NoOp

-- Atomic expression can be variable, number, constructor or
-- parenthesised expression.
pAExpr = (pVar `pApply` EVar) `pOr` (pNum `pApply` ENum) `pOr`
    pConstr `pOr` pThen3 ts (pLit "(") (pExpr `pOr` pOp) (pLit ")")
        where ts _ x _ = x

pConstr :: Parser CoreExpr
pConstr = pThen4 mk_constr  (pThen3 tt (pLit "Pack") (pLit "{") pNum) 
                            (pLit ",") 
                            pNum 
                            (pLit "}")
    where tt _ _ x = x
          mk_constr tag _ arity _ = EConstr tag arity
