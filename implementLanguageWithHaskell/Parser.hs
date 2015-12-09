module Parser where

import AbstractSyntax as S
import Evaluation
import ConstraintTyping
import Text.ParserCombinators.Parsec
import Data.Either.Unwrap (fromRight)



-------------------------PARSING-------------------------
-- Note: a parser is a function 
-- that takes a string and returns 
-- a structure as output

-- parser combinators are functions that 
-- accept several parsers and return a 
-- new parser as its output

-- so we will make a lot of little parsers and
-- combine them to make more complicated parsers
-- using the Parsec library

-- From page 5 of the HW 4 sheet:
parserArr = noSpace (string "arr")

parserLpar = noSpace (string "(")

parserRpar = noSpace (string ")")

-- return what is in the parenthesis
parserParens pa =
	do
		parserLpar
		a <- pa
		parserRpar
		return a

parserComma = noSpace (string ",")

parserColon  = noSpace (string ":")

parserFullstop = noSpace (string ".") -- period

parserFi = noSpace (string "fi")

keywordSet = ["arr",",",":",".","fi","abs","app","Bool","Nat","true","false","if","then","else","0","succ","pred","iszero"]

parserIdentifier::Parser Term
parserIdentifier = do
	x <- noSpace (many1 lower)
	--if x has key words, error!
	return (Identifier x)
    -- note: many1 p applies the parser p one or more times (http://hackage.haskell.org/package/parsec-3.1.9/docs/Text-Parsec-Combinator.html)
    -- note: lower parses a lower case character (http://hackage.haskell.org/package/parsec-3.1.9/docs/src/Text-Parsec-Char.html#spaces)

parserExplicitAbs :: Parser Term
parserExplicitAbs = 
	do
		noSpace (string "abs")
		parserLpar
		name <- parserIdentifier
		parserColon
		type1 <- parserType
		parserFullstop
		term1 <- parserTerm
		parserRpar
		return (Abstraction name type1 term1)

-- find the used type variables in a term
-- return these type variables in a list
-- this function is necessary for generating fresh type variables because we can't use them again
-- eg: usedTypeVariables (S.If S.Tru S.Fls S.Fls) = []
-- eg: usedTypeVariables (S.Abstraction (S.Identifier "a") (S.TyVar "X") S.Tru) =["X"]
usedTypeVariables :: S.Term -> [S.TypeVar]
usedTypeVariables (S.Abstraction t1 t2 t3) = (usedTypeVariablesHelper t2) ++ (usedTypeVariables t3) -- t1 is variable, t2 is variable type and t3 is body
	where
		usedTypeVariablesHelper :: S.Type ->[S.TypeVar]
		usedTypeVariablesHelper (S.TyVar name) = [name]
		usedTypeVariablesHelper (S.TypePair t1 t2) = (usedTypeVariablesHelper t1) ++ (usedTypeVariablesHelper t2)
usedTypeVariables (S.Application t1 t2) = (usedTypeVariables t1) ++ (usedTypeVariables t2)
usedTypeVariables (S.If t1 t2 t3) = (usedTypeVariables t1) ++ (usedTypeVariables t2) ++ (usedTypeVariables t3) 
usedTypeVariables (S.Succ t) = (usedTypeVariables t)
usedTypeVariables (S.Pred t) = (usedTypeVariables t)
usedTypeVariables (S.IsZero t) = (usedTypeVariables t)
usedTypeVariables (S.Fix t) = (usedTypeVariables t)
usedTypeVariables _ = [ ]

moar_variables :: [S.TypeVar]
moar_variables = map (\x -> [x]) ['a'..'z']

-- generate fresh variables given a term
-- fresh variables need to be in the set of variables defined above
-- and cannot be in used variables of the given term
-- eg: generateFreshVariable (S.Abstraction (S.Identifier "b") (S.TyVar "A") S.Tru) = B
-- note: this is like saying (lambda b:X . True)
generateFreshVariable :: S.Term -> S.Type
generateFreshVariable term = head [S.TyVar x | x <- moar_variables, not (elem x utvs)]
	where utvs = usedTypeVariables term

parserImplicitAbs :: Parser Term
parserImplicitAbs = 
	do
		noSpace (string "abs")
		parserLpar
		name <- parserIdentifier
		parserFullstop
		term1 <- parserTerm
		parserRpar
		return (Abstraction name (generateFreshVariable term1) term1)



-- looks thru the let term and updates the var names
replaceVars :: (Term, Int) -> (Term, Int)
replaceVars ((Abstraction t1 t1Type body), idx) = case t1Type of
											(TyVar name) -> (Abstraction t1 (TyVar (name ++ show (idx))) (fst (replaceVars (body, idx))), idx)
											otherwise -> (Abstraction t1 t1Type (fst (replaceVars (body, idx))), idx)

replaceVars ((Application t0 t1),idx) = (Application (fst (replaceVars (t0, idx))) (fst (replaceVars (t1, idx))),idx)
replaceVars ((If t0 t1 t2),idx) =  (If (fst (replaceVars (t0, idx))) (fst (replaceVars (t1, idx))) (fst (replaceVars (t2, idx))),idx)
replaceVars ((Pred t),idx) =  (Pred (fst (replaceVars (t, idx))),idx)
replaceVars ((Succ t),idx) =  (Succ (fst (replaceVars (t, idx))),idx)
replaceVars ((IsZero t),idx) =  (IsZero (fst (replaceVars (t, idx))),idx)
replaceVars ((Fix t),idx) =  (Fix (fst (replaceVars (t, idx))),idx)
replaceVars (a, idx) = (a, idx)






-- looks for a var to replace with the let term
subFV :: Term -> Term -> Term -> Int -> (Term,Int)
subFV (Abstraction t0 aType t1) var val idx
	| var == t0 = ((Abstraction t0 aType t1), idx)
	| otherwise = ((Abstraction t0 aType t1'), tidx)
	where 
		(t1', tidx) = subFV t1 var val idx
subFV (Application t0 t1) var val idx = 
	let 
		(t0', tidx1) = subFV t0 var val idx
		(t1', tidx2) = subFV t1 var val tidx1
	in 
		((Application t0' t1'), tidx2)

subFV (If t0 t1 t2) var val idx = 
	let 
		(t0', tidx1) = subFV t0 var val idx
		(t1', tidx2) = subFV t1 var val tidx1
		(t2', tidx3) = subFV t2 var val tidx2
	in 
		((If t0' t1' t2'), tidx3)
subFV (Succ t) var val idx = 
	let 
		(t', tidx) = subFV t var val idx
	in 
		((Succ t'), tidx)

subFV (Pred t) var val idx = 
	let 
		(t', tidx) = subFV t var val idx
	in 
		((Pred t'), tidx)

subFV (IsZero t) var val idx = 
	let 
		(t', tidx) = subFV t var val idx
	in 
		((IsZero t'), tidx)

subFV (Fix t) var val idx = 
	let 
		(t', tidx) = subFV t var val idx
	in 
		((Fix t'), tidx)
subFV term1 var term2 idx
	| var == term1 = (fst (replaceVars (term2,idx)), idx+1)
	| otherwise = (term1, idx)




parserLet :: Parser Term
parserLet = 
	do
		noSpace (string "let")
		varName <- parserIdentifier
		noSpace (string "=")
		t1 <- parserTerm
		noSpace (string "in")
		t2 <- parserTerm
		return (fst(subFV t2 varName t1 0))

parserType :: Parser Type 
parserType = 
	do
		noSpace (string "Bool") 
		return TyBool
	<|>
	do
		noSpace (string "Nat")
		return TyNat
	<|>
	do
		parserArr
		parserLpar
		t1 <- parserType
		parserComma
		t2 <- parserType
		parserRpar
		return (TypePair t1 t2)

parserTerm = 
	do
		try $ parserLet
	<|>
	do 
		try $ parserFix
	<|>
	do
		try $ parserIfthenelse 
	<|>	
	do
		try $ parserIszero  
	<|> 
	do
		try $ parserExplicitAbs 
	<|>
	do
		try $ parserImplicitAbs
	<|> 
	do
		try $ parserApp
	<|> try (parserBool) <|> try (parserNat) <|> try (parserParens parserTerm) <|> try (parserIdentifier)
	-- note: the try parser behaves like parse p but doesn't consume input when p fails (http://book.realworldhaskell.org/read/using-parsec.html)

parserApp = 
	do
		noSpace (string "app")
		parserLpar
		t1 <- parserTerm
		parserComma
		t2 <- parserTerm
		parserRpar
		return (Application t1 t2)

parserTrue = noSpace (string "true")

parserFalse = noSpace (string "false")

parserIf = noSpace (string "if")

parserThen = noSpace (string "then")

parserElse = noSpace (string "else")

parserIfthenelse = 
	do
		parserIf
		t1 <- parserTerm
		parserThen
		t2 <- parserTerm
		parserElse
		t3 <- parserTerm
		parserFi
		return (If t1 t2 t3)

parserZero = noSpace (string "0")

parserSucc = do
	noSpace (string "succ")
	t <- parserParens parserTerm
	return (Succ t)

parserPred = do
	noSpace (string "pred")
	t <- parserParens parserTerm
	return (Pred t)

parserIszero = 
	do
		noSpace (string "iszero")
		t <- parserParens parserTerm
		return (IsZero t)

parserFix = 
	do
		noSpace (string "fix")
		t <- parserParens parserTerm
		return (Fix t)

parserBool :: Parser Term
parserBool =
	(parserTrue >> return Tru) <|> (parserFalse >> return Fls) 
	-- note: left <|> right will only evaluate right if left fails (http://research.microsoft.com/pubs/65201/parsec-paper-letter.pdf)
	-- note: x >> y passes results of the first into the second (https://www.haskell.org/tutorial/monads.html)

parserNat:: Parser Term
parserNat = (parserZero >> return Zero) <|> parserSucc <|> parserPred

-- a function for editing parsers to skip spaces
-- input: a parser
-- output: a parser that skips white spaces
noSpace :: Parser a -> Parser a
noSpace parser = do
	spaces  -- spaces skips white space characters
	a <- parser
	spaces
	return a

