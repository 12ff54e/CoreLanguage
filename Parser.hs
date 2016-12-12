module CoreLanguage.Parser where

import CoreLanguage.Base

-- | A parser is composition of clexical analyser
-- and syntax analyser.
--parse :: String -> CoreProgram
--parse = syntax . clex (0,0)

clex :: (Int,Int) -> String -> [Token]
--syntax :: [Token] -> CoreProgram

-- | tokens with its line and column number
type Token = ((Int,Int),String)

-- | parser take a list of tokens and return 
-- all possibles of "word" it recognized, 
-- paired with remaining list of tokens.
type Parser a = [Token] -> [(a,[Token])]

------------------------------------------------

-- | The clexical analyser breaks the input string
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
    | isComment h2 = clex (row+1,0) cRes
    | isDigit c = ((row,col),c:num_t) : clex (row,1+col+length num_t) nRes
    | isLetter c = ((row,col),c:var_t) : clex (row,1+col+length var_t) vRes
    | isTwoCharOp op2 = ((row,col),op2) : clex (row,2+col) oRes
    | otherwise = ((row,col),[c]) : clex (row,1+col) cs
        where   h2 = [c,head cs]
                cRes = dropWhile (/= '\n') cs
                (num_t,nRes) = span isDigit cs
                (var_t,vRes) = span isVarChar cs
                op2 = [c,head cs]
                oRes = tail cs

-- | functions judging a char belongs to specific field
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

-- | construct a parser that take the first token if
-- it satisfied the predict, and return empty list if failed
pSat :: (Token -> Bool) -> Parser String
pSat prd [] = []
pSat prd (tok:toks)
    | prd tok = [(snd tok, toks)]
    | otherwise = []

-- | construct a parser equivalent to apply the function to the origin
-- parser's result
pApply :: Parser a -> (a->b) -> Parser b
pApply p f toks = [ (f x,toks') | (x,toks') <- p toks ]

-- | a parser for variables
pVar :: Parser (Expr a)
pVar = pSat (\(_,tok) -> isLetter $ head tok) `pApply` EVar

-- | a parser for number
pNum :: Parser (Expr a)
pNum = pSat (\(_,tok) -> isDigit $ head tok) `pApply` 
        \num -> ENum (read num :: Int)

-- | combine two parser p1 and p2 to contruct a "p1 or p2" parser
pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 toks = (p1 toks) ++ (p2 toks)

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
    [ (f v1 v2 v3, toks2) | (v1, toks1) <- p1 toks,
                            (v2, toks2) <- p2 toks1,
                            (v3, toks3) <- p3 toks2 ]

-- | extend pThen to accept four parsers
pThen4  :: (a -> b -> c -> d -> e) 
        -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
pThen4 f p1 p2 p3 p4 toks = 
    [ (f v1 v2 v3 v4, toks2) |  (v1, toks1) <- p1 toks,
                                (v2, toks2) <- p2 toks1,
                                (v3, toks3) <- p3 toks2,
                                (v4, toks4) <- p4 toks3 ]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = (pOneOrMore p) `pAlt` (pEmpty [])

pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p toks = [(x:y,toks2) |  (x, toks1) <- p toks,  
                                    (y, toks2) <- pZeroOrMore p toks1 ]

--pOneOrMoreWithSpt :: Parser a -> Parser b -> Parser [a]
--pOneOrMoreWithSpt pct pspt = 

