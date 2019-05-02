module language
%default total
%access public export


data IntExpr =
  IntLiteral Nat
  | IntVar String
  | Plus IntExpr IntExpr
  | Minus IntExpr IntExpr
  | Times IntExpr IntExpr


data BoolExpr =
  Equals IntExpr IntExpr
  | LessThan IntExpr IntExpr
  | Divides IntExpr IntExpr
  | Neg BoolExpr


data Instruction =
  Assign String IntExpr
  | Seq Instruction Instruction
  | While BoolExpr Instruction
  | If BoolExpr Instruction


evalInt : (String -> Nat) -> IntExpr -> Nat
evalInt valueOf (IntLiteral val) = val
evalInt valueOf (IntVar name) = valueOf name
evalInt valueOf (Plus lhs rhs) = (evalInt valueOf lhs) + (evalInt valueOf rhs)
evalInt valueOf (Minus lhs rhs) = minus (evalInt valueOf lhs) (evalInt valueOf rhs)
evalInt valueOf (Times lhs rhs) = (evalInt valueOf lhs) * (evalInt valueOf rhs)


divides : Nat -> Nat -> Type
divides x y = (k : Nat ** (k * x = y))

greatestCommonDivider : Nat -> Nat -> Nat -> Type
greatestCommonDivider x y d = ((divides d x), (divides d y),
  {largestDiv : Nat} -> (((LT d largestDiv),(divides largestDiv x), (divides largestDiv y))) -> Void)

evalBool : (valueOf : String -> Nat) -> (expr : BoolExpr) -> Type
evalBool valueOf (LessThan x y) = LT (evalInt valueOf x) (evalInt valueOf y)
evalBool valueOf (Divides x y) = divides (evalInt valueOf x) (evalInt valueOf y)
evalBool valueOf (Equals x y) = (evalInt valueOf x) = (evalInt valueOf y)
evalBool valueOf (Neg e) = Not (evalBool valueOf e)


data Assertion =
  PredAssert String (List IntExpr)
  | BoolAssert BoolExpr
  | AndAssert Assertion Assertion
  | OrAssert Assertion Assertion
  | NotAssert Assertion
  | TrueAssert
  | FalseAssert
  | GCDEQ IntExpr IntExpr IntExpr IntExpr


evalAssert: (String -> (List Nat) -> Type) -> (String -> Nat) -> Assertion -> Type
evalAssert valueOfPred valueOfInt (PredAssert predName params) = valueOfPred predName (map (evalInt valueOfInt) params)
evalAssert valueOfPred valueOfInt (BoolAssert expr)   = (evalBool valueOfInt expr)
evalAssert valueOfPred valueOfInt (AndAssert x y)     = (evalAssert valueOfPred valueOfInt x, evalAssert valueOfPred valueOfInt y)
evalAssert valueOfPred valueOfInt (OrAssert x y)      = Either (evalAssert valueOfPred valueOfInt x) (evalAssert valueOfPred valueOfInt y)
evalAssert valueOfPred valueOfInt (NotAssert x)       = Not (evalAssert valueOfPred valueOfInt x)
evalAssert valueOfPred valueOfInt TrueAssert          = ()
evalAssert valueOfPred valueOfInt FalseAssert         = Void
evalAssert valueOfPred valueOfInt (GCDEQ xExpr yExpr aExpr bExpr)
  = (gcd : Nat ** ((greatestCommonDivider x y gcd), (greatestCommonDivider a b gcd))) where
    x : Nat
    x = evalInt valueOfInt xExpr
    y : Nat
    y = evalInt valueOfInt yExpr
    a : Nat
    a = evalInt valueOfInt aExpr
    b : Nat
    b = evalInt valueOfInt bExpr

data AnnotatedInst =
  Pre Assertion AnnotatedInst
  | A_Assign String IntExpr
  | A_Seq AnnotatedInst AnnotatedInst
  | A_While BoolExpr Assertion AnnotatedInst
  | A_If BoolExpr AnnotatedInst AnnotatedInst


intSubst: (varName : String) -> (replacement: IntExpr) -> (expr: IntExpr) -> IntExpr
intSubst varName replacement (IntLiteral x) = IntLiteral x
intSubst varName replacement (Plus x y) = Plus (intSubst varName replacement x) (intSubst varName replacement y)
intSubst varName replacement (Minus x y) = Minus (intSubst varName replacement x) (intSubst varName replacement y)
intSubst varName replacement (Times x y) = Times (intSubst varName replacement x) (intSubst varName replacement y)
intSubst varName replacement (IntVar x) with (decEq x varName)
  intSubst varName replacement (IntVar x) | (Yes _) = replacement
  intSubst varName replacement (IntVar x) | (No _) = IntVar x


boolSubst : (varName : String) -> (replacement : IntExpr) -> (expr : BoolExpr) -> BoolExpr
boolSubst varName replacement (LessThan x y) = LessThan (intSubst varName replacement x) (intSubst varName replacement y)
boolSubst varName replacement (Divides x y) = Divides (intSubst varName replacement x) (intSubst varName replacement y)
boolSubst varName replacement (Equals x y) = Equals (intSubst varName replacement x) (intSubst varName replacement y)
boolSubst varName replacement (Neg e) = Neg (boolSubst varName replacement e)

subst : (varName : String) -> (replacement : IntExpr) -> (assert : Assertion) -> Assertion
subst varName replacement (PredAssert predName predParams) = PredAssert predName (map (intSubst varName replacement) predParams)
subst varName replacement (BoolAssert boolExpr) = BoolAssert (boolSubst varName replacement boolExpr)
subst varName replacement (AndAssert x y) = AndAssert (subst varName replacement x) (subst varName replacement y)
subst varName replacement (OrAssert x y) = OrAssert (subst varName replacement x) (subst varName replacement y)
subst varName replacement (NotAssert x) = NotAssert (subst varName replacement x)
subst varName replacement TrueAssert = TrueAssert
subst varName replacement FalseAssert = FalseAssert
subst varName replacement (GCDEQ x y a b) = GCDEQ (sHelper x) (sHelper y) (sHelper a) (sHelper b) where
  sHelper : IntExpr -> IntExpr
  sHelper = intSubst varName replacement

precondition : (instr : AnnotatedInst) -> (post : Assertion) -> Assertion
precondition (Pre pre i) post = pre
precondition (A_Assign varName expr) post = subst varName expr post
precondition (A_Seq i1 i2) post = precondition i1 (precondition i2 post)
precondition (A_While expr invariant body) post = invariant
precondition (A_If cond iThen iElse) post =
  OrAssert
    (AndAssert (BoolAssert cond) (precondition iThen post))
    (AndAssert (NotAssert (BoolAssert cond)) ((precondition iThen post)))

data Implication = Implies Assertion Assertion

verificationCondition : (inst : AnnotatedInst) -> (post : Assertion) -> List Implication
verificationCondition (Pre pre i) post = (Implies pre (precondition i post))::(verificationCondition i post)
verificationCondition (A_Assign _ _) _ = []
verificationCondition (A_Seq x y) post = (verificationCondition x post) ++ (verificationCondition y post)
verificationCondition (A_While expr invariant body) post = (Implies (AndAssert (BoolAssert expr) invariant) (precondition body invariant)) ::
                                                            (Implies(AndAssert (NotAssert (BoolAssert expr)) invariant) post)::
                                                            verificationCondition body invariant
verificationCondition (A_If _ _ _) post = []


valid : (predValue : String -> List Nat -> Type) -> (conditions : List Implication) -> Type
valid predValue [] = ()
valid predValue ((Implies x y) :: xs) =
  ((map : String->Nat) -> (evalAssert predValue map x) -> (evalAssert predValue map y),
  valid predValue xs)

simplePredVal : String -> List Nat -> Type
simplePredVal x xs = ()
