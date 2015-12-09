module AbstractSyntax where

-------------------------DEFINITIONS-------------------------

-- define the terms
-- pulled from HW 5
data Term = Identifier {name :: String} 									   -- variable
	      | Abstraction {variable :: Term, variableType :: Type, body :: Term} -- abstraction     lambda variable: Type. body
	      | Application Term Term  										       -- application
	      | Tru 															   -- constant true
	      | Fls   															   -- constant false
	      | If Term Term Term 												   -- conditional
	      | Zero 															   -- constant zero
	      | Succ Term 														   -- successor
	      | Pred Term 														   -- predecessor
	      | IsZero Term 													   -- zero test
	      | Fix Term
	      deriving (Eq)

-- show the terms defined above
-- pulled from HW 5
instance Show Term where
	show Tru = "True"
	show Fls = "False"
	show (If p c a) = "If " ++ show p ++ " then " ++ show c ++ " else " ++ show a
	show Zero = "0"
	show (Succ t) | isNumericValue t = showAsNum t 1
	              | otherwise = "(succ " ++ show t ++ ")"
	              where showAsNum Zero num = show num
	                    showAsNum (Succ t) num = showAsNum t (num + 1)
	show (Pred t) = "(pred " ++ show t ++ ")"   
	show (IsZero t) = "iszero " ++ show t
	show (Identifier n) = n
	show (Abstraction v vt b) = "abs (" ++ (show v) ++ ":" ++ (show vt) ++ "." ++ (show b) ++ ")"
	show (Application t1 t2) = "app (" ++ (show t1) ++ "," ++ (show t2) ++ ")"
	show (Fix t) = "fix(" ++ (show t) ++ ")"
	show (t) = "(" ++ (show t) ++ ")"

-- define the types
data Type = TypePair {t1 :: Type, t2 :: Type}  -- types of functions
          | TyBool 							   -- types of booleans
          | TyNat                              -- types of natural numbers 
          | TyVar TypeVar                      -- types of type variables
          deriving (Eq)

type TypeVar = String

-- show the types defined above
instance Show Type where
	show (TypePair a b) = "arr (" ++ (show a) ++ "," ++ (show b) ++ ")"
	show TyBool = "Bool"
	show TyNat = "Nat"
	show (TyVar varName) = varName

-- define the typing context
data TypeContext = Empty  										-- empty context
				 | VariableBindings {bindings :: [Binding]}     -- term variable binding


-- this structure is used in TypeContext
-- define the bindings of variables to their types in some sort of term
-- eg : x: Bool has x as the identifierName and Bool as the identifierType
data Binding = VarBind {identifierName :: String, identifierType :: Type} deriving (Eq)

-- input: a term
-- output: whether or not the term is a value
-- pulled from HW 5
isValue :: Term -> Bool
isValue (Abstraction _ _ t) = True
isValue Tru = True
isValue Fls = True
isValue t = isNumericValue t
isValue _ = False

-- input: a term
-- output: whether or not the term is a numeric value 
-- pulled from HW 5
isNumericValue :: Term -> Bool
isNumericValue Zero = True
isNumericValue (Succ t) = isNumericValue t
isNumericValue _ = False