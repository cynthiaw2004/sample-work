module Unification where

import Data.List(find)

-- on paper, terms are 
-- constant symbols and variables
-- if t1,...tn are terms and f is in An then f(t1,...tn) is a term
-- f(t1...tn) is represented by Fun f [t1 t2 ...tn]
-- variable v is represented by Var v
data Term v f = Fun f [Term v f] | Var v deriving (Show,Eq)

-- the equation is the lhs = rhs
type Equation v f = (Term v f, Term v f)

-- variable v is equal to term v f
-- essentially v will be replaced with Term v f
type Binding v f = (v,Term v f) 

-- a substitution is a list of bindings
type Substitution v f = [Binding v f] 

data EquationOutcome = HaltWithFailure | HaltWithCycle | NoMatch | Success deriving (Show,Eq)

-- given a term (a variable or a function) and a substitution list (theta), 
-- apply it to the term and output the resulting term
-- The find function takes a predicate and a structure and returns 
-- the leftmost element of the structure matching the predicate, 
-- or Nothing if there is no such element

-- in this situation, find is given a predicate that checks if the first
-- element in a given pair is equal to the variable x
-- it then checks every binding in the substitution list beta
-- and sees if it fulfills the predicate
-- Nothing means no substitution takes place
-- Just (_,t) means one substitution takes place: x is replaced with 
-- corresponding 2nd element in the pair

-- given a function it applies the substitution for each of the args
-- in the function
applySubst :: (Eq v, Eq f) => Term v f -> Substitution v f -> Term v f
applySubst (Var x) theta = 
	case Data.List.find (\(z,_) -> z == x) theta of 
		Nothing    -> Var x
		Just (_,t) -> t
applySubst (Fun f tlist) theta = Fun f (map (\t -> applySubst t theta) tlist)

-- given a list of equations, apply the given sub list to the equations and
-- output the resulting equations
applySubst' :: (Eq v, Eq f) => [Equation v f] -> Substitution v f -> [Equation v f]
applySubst' eql [] = eql
applySubst' [] theta = []
applySubst' eql theta = map (\(s,t) -> (applySubst s theta, applySubst t theta)) eql


-- given a list of equations and a list of subs, 
-- apply all the subs to the equations from back to front
-- and return the resulting equation list
applySubsts :: (Eq v, Eq f) => [Equation v f] -> [Substitution v f] -> [Equation v f]
applySubsts eql [] = eql
applySubsts eql ys = applySubsts (applySubst' eql x) xs
	where (x:xs) = reverse ys


-- the unify that the professor really wants and to follow the cbt template...
-- given a list of equations, unifies them and returns
-- the outcome and the substitution list converted as an equation list 
unify :: (Eq v,Eq f) => [Equation v f] -> (EquationOutcome,[Equation v f])
unify eql = 
	let 
		(outcome,subs) = trueunify eql
		subeqns = convert_subeqns subs
	in
		(outcome,subeqns)


-- given a list of subs, converts them into equations
-- this is helper equation to conver a list of substitutions
-- into a list of equations which is necessary for
-- the professor's unify template
convert_subeqns :: (Eq v, Eq f) => [Substitution v f] -> [Equation v f]
convert_subeqns [] = []
convert_subeqns (x:xs) = 
	let 
		a = fst (head x)
		b = snd (head x)
	in
		[(Var a,b)] ++ convert_subeqns xs


-- DIFFERS FROM TEACHER'S IMPLEMENTATION IN THAT
-- THE TYPE RETURNED IS A LIST OF SUBS
-- AND NOT A LIST OF EQNS
-- DEFINITIONALLY, THIS IS MORE CORRECT
-- given a list of equations, unifies them and returns the list of substitutions
-- and the equation outcome
trueunify :: (Eq v, Eq f) => [Equation v f] -> (EquationOutcome,[Substitution v f])
trueunify eql = (outcome,subs)
	where (outcome,equationList,subs) = unifySub eql []

-- given a list of equations, unifies them and returns the
-- equation outcome, the resulting equation list (should be empty)
-- and the list of substitutions
unifySub :: (Eq v, Eq f) => [Equation v f] -> [Substitution v f] -> (EquationOutcome,[Equation v f],[Substitution v f])
unifySub (e:es) subs
	| and [outcome == Success,resultEquations /= []]            = unifySub (applySubsts resultEquations resultSub) (resultSub ++ subs)       -- outcome is success,there are eqns -> apply subs and keep unifying
	| and [outcome == Success,resultEquations == []]            = (outcome,applySubsts resultEquations resultSub,resultSub ++ subs)     -- outcome success, no eqns          -> apply subs and  done
	| outcome /= Success                                        = (outcome,resultEquations,resultSub ++ subs)
	where (outcome,resultEquations,resultSub) = unify1 (e:es)      

  
-- given equation list, manip first element only
-- returns the outcome, the equation list, the sub list
unify1 :: (Eq v, Eq f) => [Equation v f] -> (EquationOutcome,[Equation v f],[Substitution v f])

-- ALGORITHM 1 PART A (pg 261)
-- equation of form t = x 
-- where t is not a variable and x 
-- is a variable and rewrite it as x = t
unify1 ((Fun a b, Var c):eqns) = (Success,((Var c, Fun a b):eqns),[])

-- ALGORITHM 1 PART B 
-- equation of form x = x
-- where x is a variable and erase it
-- otherwise make it a substitution
-- and continue unifying
unify1 ((Var a,Var b):eqns)
	| a == b    = (Success,eqns,[])
	| otherwise = (Success,((Var a,Var b):eqns),[[(a, Var b)]])

-- ALGORITHM 1 PART C
-- equation of the form
-- t' = t'' where t' and t'' are not variables
-- if the two root function symbols are different, 
-- stop with failure; otherwise apply term reduction
-- ie:
-- term reduction:
-- f(t1,t2...tn) = f(s1,s2...sn) -> t1=s1, t2=s2,...tn=sn
-- fail:
-- f(t1,t2...tn) = g(s1,s2...sn) and f neq g -> fail
unify1 ((Fun a b, Fun c d):eqns)
	| a /= c                  = (HaltWithFailure,((Fun a b, Fun c d):eqns), [])
	| length (b) /= length(d) = (NoMatch,((Fun a b,Fun c d):eqns), [])
	| otherwise               = (Success, (zip b d) ++ eqns, [])

-- ALGORITHM 1 PART D
-- equation of the form x = t where x is
-- a variable which occurs somewhere else in the set
-- of equations and where t neq x
-- if x occurs in t, fail with cycle
-- otherwise apply variable elimination (apply the
-- substitution (t,x) to all other equations in 
-- the set without deleting x =t equation)
unify1 ((Var a,Fun b c):eqns) 
	| isInside (Var a) (Fun b c) = (HaltWithCycle,((Var a, Fun b c):eqns),[])
	| otherwise                  = (Success,((Var a, Fun b c):eqns),[[(a,Fun b c)]])

-- no cases apply
unify1 [] = (Success,[],[])

-- checks if the 1st argument (a variable)
-- in inside the 2nd argument (a function)
-- True if yes, False if no
-- note that or someList returns True if some element 
-- inside someList is True
isInside :: (Eq v, Eq f) => Term v f -> Term v f -> Bool
isInside (Var a) (Fun b c)
	|elem (Var a) c  = True
	|otherwise       = or (map (isInside (Var a)) c) 
isInside _ _ = False



-- for testing unification

-- problem in hw sheet
-- halt with cycle
s1 = Fun "f" [Fun "g" [Fun "a" [],Var "X"],Fun "h" [Fun "f" [Var "Y",Var "Z"]]]
s2 = Fun "g" [Var "Y",Fun "h" [Fun "f" [Var "Z",Var "U"]]]
t1 = Fun "f" [Var "U",Fun "h" [Fun "f" [Var "X",Var "X"]]]
t2 = Fun "g" [Fun "f" [Fun "h" [Var "X"], Fun "a" [ ]],Fun "h" [Fun "f" [Fun "a" [],Fun "b" []]]]
problem = [(s1,t1),(s2,t2)]

--martelli paper
-- example
-- success
a1 = Fun "g" [Var "X2"]
a2 = Fun "f" [Var "X1",Fun "h" [Var "X1"],Var "X2"]
b1 = Var "X1"
b2 = Fun "f" [Fun "g" [Var "X3"],Var "X4",Var "X3"]
problem1 = [(a1,b1),(a2,b2)]

-- example
-- halt with no match
m1 = Fun "g" [Var "X2"]
n1 = Fun "g" [Var "X3",Var "X1"]
problem2 = [(m1,n1)]

-- example
-- halt with failure
q1 = Fun "g" [Var "x1"]
l1 = Fun "f" [Var "x1"]
problem3 = [(q1,l1)]

-- example
-- success
z1 = Fun "P" [Var "a",Var "y"]
z2 = Fun "P" [Var "x",Fun "f" [Var "b"]]
problem4  = [(z1,z2)]

-- example
-- success
z11 = Fun "P" [Var "a",Var "x",Fun "f" [Fun "g" [Var "y"]]]
z12 = Fun "P" [Var "z",Fun "f" [Var "z"],Fun "f" [Var "u"]]
problem5 = [(z11,z12)]