module Evaluation where 

import AbstractSyntax
import Data.Monoid


-------------------------EVALUATION-------------------------

-- the one step evaluation relation
-- input: a term
-- output: (Nothing,Context) or a (Maybe Term,Context) after 1 evaluation step
-- similar to HW 4 except we take fix into account
eval1 :: TypeContext -> Term -> (Maybe Term,TypeContext) 
eval1 context (Application t1 t2)
	| not(isValue t1)                       = recursorCon (\t -> Application t t2) t1 context -- E APP1
	| (isValue t1) && (not(isValue t2))     = recursorCon (\t -> Application t1 t) t2 context -- E APP2
	| otherwise                             = case t1 of 
												Abstraction var varType absBody -> (Just (sub absBody var t2),(addBinding context var varType)) -- E APP ABS
												otherwise                       -> (Nothing, context)
eval1 context (If Tru t2 t3) = (Just t2, context)                             -- E-IFTRUE rule
eval1 context (If Fls t2 t3) = (Just t3,context)                              -- E-IFFALSE rule
eval1 context (If t1 t2 t3) = recursorCon (\t -> If t t2 t3) t1 context       -- E-IF rule
eval1 context (Succ t) = recursorCon Succ t context			                  -- E-SUCC rule
eval1 context (Pred Zero) = (Just Zero,context)                               -- E-PREDZERO rule
eval1 context(Pred (Succ v))                                                  -- E-PREDSUCC rule
	| isNumericValue v == True = (Just v,context)
eval1 context (Pred t) = recursorCon Pred t context		                      -- E-PRED
eval1 context (IsZero Zero) = (Just Tru,context)                              -- E-ISZEROZERO rule
eval1 context (IsZero (Succ v))                                               -- E-ISZEROSUCC rule
	| isNumericValue v == True = (Just Fls,context)
	| otherwise                = (Nothing,context)
eval1 context (IsZero t) = recursorCon IsZero t context	                      -- E-ISZERO rule
eval1 context (Fix t1) = case t1 of (Abstraction var varType absBody) -> (Just(sub absBody var (Fix t1)),context) -- E-FIX BETA rule 
                                    otherwise                         -> recursorCon Fix t1 context -- E-FIX rule
eval1 context _ = (Nothing,context)		
-- sub absBody var fix t1 will replace free occurences of var with fix t1 in the absBody

-- helper function for recursorCon
-- input: a function that normally cannot be applied to monads
-- output: the function that can be applied to monads
-- pulled from HW 5
liftM :: (Monad m) => (a->b) -> m a -> m b
liftM f m1   = do { x1 <- m1; return (f x1) }

-- helper function for eval1
-- input: a function and a term and a typing context
-- output: evaluates the term by one step and applies the monadic function to it
-- pulled from HW 5
recursorCon :: (Term -> Term) -> Term -> TypeContext -> (Maybe Term,TypeContext)
recursorCon f t context = ((liftM f) term,context2)
	where (term,context2) = (eval1 context t)

-- helper function for eval1
-- input: abstraction body term, variable term, term to replace variable with
-- output: the abstraction body where all free occurences the first term are replaced with a second term
-- sub absBody var t2 will replace free occurences of var with t2 in the absBody
-- pulled from HW 5
sub :: Term -> Term -> Term -> Term
sub (Abstraction t0 t0type body) t absBody 
	| t0 == t   = Abstraction t0 t0type body -- BOUND! Can only replace free variables!
	| otherwise = Abstraction t0 t0type (sub body t absBody) 
sub (Application t0 t1) t absBody = Application (sub t0 t absBody) (sub t1 t absBody) 
sub (If t0 t1 t2) t absBody = If (sub t0 t absBody) (sub t1 t absBody) (sub t2 t absBody)
sub (Succ t0) t absBody = Succ (sub t0 t absBody)
sub (Pred t0) t absBody = Pred (sub t0 t absBody)
sub (IsZero t0) t absBody = IsZero (sub t0 t absBody)
sub (Fix t0) t absBody = Fix (sub t0 t absBody)
sub aTerm t absBody        
	|aTerm == t = absBody
	|otherwise  = aTerm

-- see Chapter 10 of TAPL's addBinding function
-- helper function for eval1
-- input: the current type context used, the term that has the new binding, the new binding type for that term
-- output: the current type context along with the new term and its binding
addBinding :: TypeContext -> Term -> Type -> TypeContext
addBinding Empty (Identifier x) t  = VariableBindings [VarBind x t]  -- a new context environment with only that new binding
addBinding notEmptyContext (Identifier x) t = VariableBindings ((VarBind x t):(bindings notEmptyContext)) -- simply cons the new binding to the existing context environment
addBinding someContext something t = error("You cannot add a binding to a non identifier to the current context")


-- multistep evaluation  
-- input: the typing context, the term to evaluate
-- output: the term evaluated as much as possible using eval1
-- pulled from HW 5
eval :: TypeContext -> Term -> Term 
eval context t 
	|isValue t = t -- nothing more to do with a value
	|otherwise = case eval1 context t of (Nothing,someContext) -> t
	                                     (Just a, nextContext) -> eval nextContext a

-------------------------TYPING-------------------------

-- see Chapter 10 TAPL's typeOf function
-- input: the typing context, a term to find the type of
-- output: the type of the term given using typing rules
detType :: TypeContext -> Term -> Type
detType someContext (Identifier x) = case (getTypeFromContext someContext (Identifier x)) of Just xtype -> xtype -- T-Var
                                                                                             Nothing    -> error("could not find type for identifier")
detType someContext (Abstraction t1 typeT1 t2) = 
	let 
		nextContext = addBinding someContext t1 typeT1 
		typeT2 = detType nextContext t2
	in
		TypePair typeT1 typeT2



detType someContext (Application t1 t2) = case (detType someContext t1) of 
									(TypePair typeT11 typeT12) -> case typeT11 of
																	(TypePair a b) -> case (detType someContext t2) of 
																						(TypePair typeT21 typeT22) -> if ((partialType typeT22) == a) then (TypePair (partialType b) (partialType typeT12)) else error("type fail both arrows")
																						_						   -> if ((detType someContext t2) == a) then (TypePair (partialType b) (partialType typeT12)) else error("type fail 1st arrow 2nd single")




																	




																	_              -> case (detType someContext t2) of
																						(TypePair typeT21 typeT22) -> if ((partialType typeT22)== typeT11) then typeT12 else error("type fail 1st single 2nd arrow")
																						_                          -> if ((detType someContext t2) == typeT11) then typeT12 else error("type fail both single")
									_                          -> error("type pair was not given") 
detType anyContext Tru = TyBool -- T-True
detType anyContext Fls = TyBool -- T-False
detType someContext (If t1 t2 t3) = if (detType someContext t1) == TyBool then (if (detType someContext t2) == (detType someContext t3) then (detType someContext t2) else error("cannot have different types for the second and third conditionals")) else error("cannot have non boolean type for first conditional") -- T-If
detType anyContext Zero = TyNat -- T-Zero
detType someContext (Succ t) = if (detType someContext t) == TyNat then TyNat else error("cannot have succ of non Nat type") -- T-Succ
detType someContext (Pred t) = if (detType someContext t) == TyNat then TyNat else error("cannot have pred of non Nat type") -- T-Pred
detType someContext (IsZero t) = if (detType someContext t) == TyNat then TyBool else error("cannot have iszero of non Nat type") -- T-IsZero
detType someContext (Fix t1) = case typet1 of (TypePair t1 t2) -> if (t1 == t2) then t1 else error("the generator function does not have the same input and output type")  
                                              _                -> error("fix was not given a generator function")
                                    where typet1 = detType someContext t1
 
 --helper function in the case of partial function application
 -- input: a type
 -- output: a type
partialType:: Type -> Type
partialType b = case b of 
	(TypePair c d) -> partialType d
	_              -> b

-- helper function for getTypeFromContext
-- input: a boolean function, a foldable structure such as a list
-- output: the leftmost element of the foldable structure that satisfies the boolean function or Nothing if no element satisfies it	
find :: Foldable t => (a -> Bool) -> t a -> Maybe a
find p = getFirst . foldMap (\ x -> First (if p x then Just x else Nothing))

-- helper function for getTypeFromContext
-- pulled from HW 5
-- input: a Maybe value 
-- output: the value inside the Maybe...if there is no value, an error occurs!
fromJust          :: Maybe a -> a
fromJust Nothing  = error("Cannot grab value from Nothing!")
fromJust (Just x) = x

-- see chapter 10 of TAPL for reference
-- helper function for detType
-- input: the typing context, the term to find the type of in the typing context
-- output: the type of the term in the typing context or Nothing if identifier type is not found
getTypeFromContext :: TypeContext -> Term -> Maybe Type
getTypeFromContext Empty (Identifier x) = Nothing
getTypeFromContext someContext (Identifier x) = resultType
	where
		typeFound = find (\str -> (identifierName str) == x) (bindings someContext)
		resultType
			| typeFound == Nothing = Nothing
			| otherwise               = Just (identifierType (fromJust typeFound))
getTypeContext _ term = error("can't find a typing context for the given term")