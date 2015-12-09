module ConstraintTyping where

import qualified AbstractSyntax as S
import qualified Unification as U
import Data.List
import Data.Maybe

-- type equation
type TypeConstraint = (S.Type,S.Type)

-- this is the constraint set which consists of
-- a set of type equations
type TypeConstraintSet = [TypeConstraint]

-- sub in the S.Type for S.TypeVar
type TypeSubstitution  = [(S.TypeVar,S.Type)]
 
type TypeUnifVar = S.TypeVar
data TypeUnifFun = TypeUnifArrow | TypeUnifBool |TypeUnifNat deriving (Eq,Show)

-- given a constraint set, encodes the type equations within 
encode :: TypeConstraintSet -> [U.Equation TypeUnifVar TypeUnifFun]
encode = map (\(tau1,tau2) -> (enctype tau1,enctype tau2))
	where
		enctype :: S.Type -> U.Term TypeUnifVar TypeUnifFun  
		enctype (S.TypePair tau1 tau2) = U.Fun TypeUnifArrow [enctype tau1,enctype tau2]
		enctype S.TyBool = U.Fun TypeUnifBool []
		enctype S.TyNat = U.Fun TypeUnifNat []
		enctype (S.TyVar xi) = U.Var xi

-- given a substitution converted to equation form, decodes it into a type substitution
decode :: [U.Equation TypeUnifVar TypeUnifFun] -> TypeSubstitution
decode = map f
	where
		f :: (U.Term TypeUnifVar TypeUnifFun,U.Term TypeUnifVar TypeUnifFun) -> (S.TypeVar,S.Type)
		f (U.Var xi,t) = (xi,g t)
		g :: U.Term TypeUnifVar TypeUnifFun -> S.Type
		g (U.Fun TypeUnifArrow [t1,t2]) = S.TypePair (g t1) (g t2)
		g (U.Fun TypeUnifBool []) = S.TyBool
		g (U.Fun TypeUnifNat []) = S.TyNat
		g (U.Var xi) = S.TyVar xi

-- given a term, derives the term's type
reconstructType :: S.Term -> Maybe S.Term
reconstructType t =
	let
		constraints = deriveTypeConstraints t -- derive the constraint set
		unifencoding = encode constraints -- encode the constraint set
		(unifoutcome,unifsolvedequations) = U.unify unifencoding -- unify the encoded constraints
	in 
		case unifoutcome of 
			U.Success -> -- if outcome of unification is successful
				let
					typesubst = decode unifsolvedequations -- decode the substitution
					t' = applyTSubToTerm typesubst t -- apply the decoded sub to the term
				in
					Just t'
			U.HaltWithFailure -> Nothing -- if outcome of unification fails
			U.HaltWithCycle -> Nothing
			U.NoMatch -> Nothing

-- CONSTRAINT RULES ON PAGE 322 IN TAPL
constraintRules :: S.Term -> Id -> IdBindingSet -> (NewId,TypeConstraintSet,IdBindingSet)

-- CT VAR
constraintRules (S.Identifier x) ident bindingSet = 
	let
		vName = removeId ident
		nextId = succ ident 
	in
		case findBinding bindingSet (S.Identifier x) of
			Just name -> (nextId,[(vName,name)],bindingSet)
			Nothing   -> (nextId,[],bindingSet)

-- CT ABS
-- if the body of abs is another abs
constraintRules (S.Abstraction variable variableType body) ident bindingSet = 
	let
		vName = removeId ident
		vName' = removeId (succ ident)
		vName'' = removeId (succ (succ ident))
		nextId = succ (succ (succ ident))
		bindingSet' = (variable,variableType):bindingSet
		(t_id,cset,bindingSet'') = constraintRules body nextId bindingSet'
		cset' = changeConstraintset cset (removeId nextId) vName''
	in
		(t_id,(vName,S.TypePair vName' vName''):(vName',variableType):cset',bindingSet'')

-- CT APP -- some sort of bug here
constraintRules (S.Application t1 t2) ident bindingSet =
	let
		vName = removeId ident
		vName' = removeId (succ ident)
		vName'' = removeId (succ (succ ident))
		nextId = succ (succ (succ ident))
		(t1_id , cset , bindingSet1) = constraintRules t1 nextId bindingSet
		c1 = changeConstraintset cset (removeId nextId) vName'
		(t2_id , cset2 , bindingSet2) = constraintRules t2 t1_id bindingSet1
		c2 = changeConstraintset cset2 (removeId t1_id) vName''
	in
		(t2_id,(vName,vName):(vName',S.TypePair vName'' vName):(c1 ++ c2),bindingSet2)

-- CT ZERO
constraintRules (S.Zero) ident bindingSet = 
	let
	 	-- generate needed variables
		vName = removeId ident
		nextId = succ ident
	in
		(nextId,[(vName,S.TyNat)],bindingSet)

-- CT SUCC
constraintRules (S.Succ t) ident bindingSet = 
	let
		-- generate needed variables
		vName = removeId ident
		vName' = removeId (succ ident)
		nextId = succ (succ ident)
		(t_id,cset,bindingSet') = constraintRules t nextId bindingSet
		cset' = 
			case t of
				S.Identifier _    -> changeConstraintset cset (removeId nextId) vName'
				S.Application _ _ -> changeConstraintset cset (removeId nextId) vName'
				otherwise         -> cset
	in
		(t_id,(vName,S.TyNat):(vName',S.TyNat):cset',bindingSet') 

-- CT PRED 
constraintRules (S.Pred t) ident bindingSet =
	let 
		-- generate needed variables
		vName = removeId ident
		vName' = removeId (succ ident)
		nextId = succ (succ ident) 
		(t_id,cset,bindingSet') = constraintRules t nextId bindingSet
		cset' = 
			case t of
				S.Identifier _    -> changeConstraintset cset (removeId nextId) vName'
				S.Application _ _ -> changeConstraintset cset (removeId nextId) vName'
				otherwise         -> cset
	in
		(t_id,(vName,S.TyNat):(vName',S.TyNat):cset',bindingSet') 

-- CT IS ZERO
constraintRules (S.IsZero t) ident bindingSet = 
	let
		-- generate needed variables
		vName = removeId ident
		vName' = removeId (succ ident)
		nextId = succ (succ ident)
		(t_id,cset,bindingSet') = constraintRules t nextId bindingSet
		cset' = 
			case t of
				S.Identifier _    -> changeConstraintset cset (removeId nextId) vName'
				S.Application _ _ -> changeConstraintset cset (removeId nextId) vName'
				otherwise         -> cset
		in
			(t_id,(vName,S.TyBool):(vName',S.TyNat):cset',bindingSet') 

-- CT TRUE
constraintRules (S.Tru) ident bindingSet = 
	let
		vName = removeId ident
		nextId = succ ident
	in 
		(nextId,[(vName,S.TyBool)],bindingSet)

-- CT FALSE
constraintRules (S.Fls) ident bindingSet = 
	let
		-- generate needed variables
		vName = removeId ident
		nextId = succ ident
	in 
		(nextId,[(vName,S.TyBool)],bindingSet)

-- CT IF
constraintRules (S.If t1 t2 t3) ident bindingSet = 
	let
		vName0 = removeId ident --v1
		vName1 = removeId (succ ident) --v2
		vName2 = removeId (succ (succ ident))--v3
		vName3 = removeId (succ (succ (succ ident)))--v0
		nextId = succ (succ (succ (succ ident)))
		(t1_id , cset0 , bindingSet1) = constraintRules t1 nextId bindingSet 
		c1 = changeConstraintset cset0 (removeId nextId) vName0
		(t2_id , cset1 , bindingSet2) = constraintRules t2 t1_id bindingSet1 
		c2 = changeConstraintset cset1 (removeId t1_id) vName1
		(t3_id , cset2, bindingSet3 ) = constraintRules t3 t2_id bindingSet2
		c3 = changeConstraintset cset2 (removeId t2_id) vName3
	in
		(t3_id,(vName0,S.TyBool):(vName1,vName2):(vName3,vName1):(c1 ++ c2 ++ c3),bindingSet3)


-- CT FIX
constraintRules (S.Fix t) ident bindingSet = 
	let
		vName0 = removeId ident
		vName1 = removeId (succ ident)
		vName2 = removeId (succ(succ ident))
		nextId = succ(succ(succ ident))
		(t_id,cset,bindingSet') = constraintRules t nextId bindingSet
	in
		(t_id,(vName0,vName1):(vName0,vName2):cset,bindingSet')



-- catchall
constraintRules left ident bindingSet = (ident,[],bindingSet)


-- now for deriving the type constraints given a term
-- follows page 322 in TAPL
-- given a term, get the contraint set
deriveTypeConstraints :: S.Term -> TypeConstraintSet
deriveTypeConstraints t  = nub (constraintSet) -- only unique solutions are allowed
	where
		(someId,constraintSet,someBindingSet) = constraintRules t (Id 'A') [] -- 'A' is our first variable in our variable list

-- binding variables types to their terms
type IdBinding = (S.Term,S.Type)
type IdBindingSet = [IdBinding]

-- given a binding set and a term (specifically a variable term),
-- will use the binding set to find
-- the type variable that matches the term
findBinding :: IdBindingSet -> S.Term -> Maybe S.Type
findBinding bindingSet (S.Identifier name) = 
	case find (\a -> (fst a) == (S.Identifier name)) bindingSet of 
		Just binding -> Just (snd binding)
		Nothing      -> Nothing 

-- these are the variables we can work with
-- ["A","B","C",...]
variables :: [S.TypeVar]
variables = map (\x -> [x]) ['A'..'Z']

-- for every type equation in the constraint set,
-- if the left hand side of the equation equals to
-- the first argument type then change the type equation in the constraint set
changeConstraintset :: TypeConstraintSet -> S.Type -> S.Type -> TypeConstraintSet
changeConstraintset constraintSet type1 type2 = [if lhs == type1 then (type2,rhs) else (lhs,rhs) | (lhs,rhs) <- constraintSet]

-- necessary for generating the next variable name 
newtype Id = Id Char deriving (Show,Eq) 
type NewId = Id

-- toVar is removeId
-- eg: toVar (Id 'b') = b
removeId :: Id -> S.Type
removeId (Id c) = S.TyVar [c]

-- fromVar is getId
-- eg: fromVar ("cccasdf") = Id 'c'
getId :: S.TypeVar -> Id
getId var = Id (head var)

-- toTypeVar is toTypeVar
-- eg: toTypeVar (Id 'c') = "c"
toTypeVar :: Id -> S.TypeVar
toTypeVar (Id c) = [c]

-- ways to:
-- get the next name in the list of potential list of names
-- 	given an id name
-- get the previous name in the list of potential list of names
-- 	given an id name
-- grab a name for an id from a list of potential names given index
-- return the index of an Id name from a list of potential names
-- Note:
-- the elemIndex function returns the index of the first element 
-- 	in the given list which is equal to the query element, 
-- 	or Nothing if there is no such element.
instance Enum Id where
	succ (Id name) = (Id (succ name))
	pred (Id name) = (Id (pred name))
	toEnum int     = Id (['A'..]!! int)
	fromEnum (Id name) = fromJust (elemIndex name ['A'..])
	
-- for applying the given subsitution to a term
applyTSubToTerm :: TypeSubstitution -> S.Term -> S.Term
applyTSubToTerm tSub (S.Abstraction var vtype body) = S.Abstraction var (subTypeVariable tSub vtype) (applyTSubToTerm tSub body)
applyTSubToTerm tSub (S.Application t1 t2) = S.Application (applyTSubToTerm tSub t1) (applyTSubToTerm tSub t2)
applyTSubToTerm tSub (S.Succ t) = S.Succ (applyTSubToTerm tSub t)
applyTSubToTerm tSub (S.Pred t) = S.Pred (applyTSubToTerm tSub t)
applyTSubToTerm tSub (S.IsZero t) = S.IsZero (applyTSubToTerm tSub t)
applyTSubToTerm tSub (S.If t1 t2 t3) = S.If (applyTSubToTerm tSub t1) (applyTSubToTerm tSub t2) (applyTSubToTerm tSub t3)
applyTSubToTerm tSub (S.Fix t) = S.Fix (applyTSubToTerm tSub t)
applyTSubToTerm tSub left = left

unifyTerm :: S.Term -> (U.EquationOutcome,[U.Equation TypeUnifVar TypeUnifFun])
unifyTerm t =
	let 
		constraintSet = deriveTypeConstraints t
		unifencoding = encode constraintSet
		(outcome,equations) = U.unify unifencoding
	in
		(outcome,equations)




-- for applying the given substituion to a type
subTypeVariable :: TypeSubstitution -> S.Type -> S.Type
subTypeVariable tsub (S.TyVar name) = 
	let
		allsubs = [asub | (var,asub) <- tsub, var == name] -- find all subs that would apply to the given type
	in
		if (length allsubs) > 0 then (subTypeVariable tsub (head allsubs)) else (S.TyVar name)
subTypeVariable tsub (S.TypePair t1 t2) = S.TypePair (subTypeVariable tsub t1) (subTypeVariable tsub t2)
subTypeVariable tsub t = t




-- tests for deriving type constraint

-- TEST FOR VAR
-- CS:
-- empty
a = S.Identifier "x"

-- TEST FOR ABS
-- x has type variable B
-- whole expression has type variable A
-- body z has type variable C
-- CS:
-- A is B to C
-- B is y
b = S.Abstraction (S.Identifier "x") (S.TyVar "y") (S.Identifier "z")

-- TEST FOR APP
-- whole expression has type variable A
-- x has type variable B
-- y has type variable C
-- CS:
-- A is A
-- B is C to A
c = S.Application (S.Identifier "x") (S.Identifier "y")

-- TEST FOR ZERO
-- whole expression has type variable A
-- CS:
-- A is Nat
d = S.Zero

-- TEST FOR SUCC
-- x has type variable A
-- whole expression has type variable B
-- CS:
-- A is Nat
-- B is Nat
e = S.Succ (S.Identifier "x")

-- TEST FOR PRED
-- x has type variable A
-- whole expression has type variable B
-- CS:
-- A is Nat
-- B is Nat
f = S.Pred (S.Identifier "x")

-- TEST FOR ISZERO
-- x has type variable B
-- whole expression has type variable A
-- CS:
-- A is Bool
-- B is Nat
g = S.IsZero (S.Identifier "x")

-- TEST FOR TRUE
-- whole expression has type variable A
-- CS:
-- A is Bool
h = S.Tru

-- TEST FOR FALSE
-- whole expression has type variable A
-- CS:
-- A is Bool
i = S.Fls

-- TEST FOR IF
-- x has type variable A, 
-- y has type variable B,
-- z has type variable C
-- whole expression has type variable D
-- CS:
-- A is Bool,
-- B is C
-- B is D
j = S.If (S.Identifier "x") (S.Identifier "y") (S.Identifier "z")

-- MORE TESTS

-- Assuming we have form If t1 t2 t3
-- t1 has type variable A
-- t2 has type variable B
-- t3 has type variable C
-- whole expression has type variable D
-- CS:
-- A is Bool
-- B is C
-- B is D
-- B is Bool (we explicitly listed it as Tru)
-- D is Bool (we explicitly listed it as Tru)
k = S.If (S.Tru) (S.Tru) (S.Tru)


-- x has type variable B
-- whole expression has type variable A
-- body has type variable C
-- term that Succ is working on has type variable E
-- CS:
-- A is B to C 
-- B is y
-- C has type Nat
-- E is y
-- E is Nat
l = S.Abstraction (S.Identifier "x") (S.TyVar "y") (S.Succ (S.Identifier "x"))

-- assuming app firstTerm secondTerm
-- whole expression has type variable A
-- first term has type variable B
-- second term has type variable C
-- abstraction is the firstTerm
-- x has type variable E
-- body z has type variable F
-- CS:
-- B is C to A
-- B is E to F
-- E is y
-- C is Bool (second term is explicitly Tru)
m = S.Application (S.Abstraction (S.Identifier "x") (S.TyVar "y") (S.Identifier "z")) (S.Tru)



-- reconstructType test

n = S.Abstraction (S.Identifier "x") (S.TyVar "y") (S.Succ (S.Identifier "x")) 

o = S.Abstraction (S.Identifier "this") (S.TyVar "y") (S.If (S.Identifier "this") (S.Zero) (S.Zero))








