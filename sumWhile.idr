module sumWhile

import language

%default total

i : String
i = "i"

iexpr : IntExpr
iexpr = IntVar i

j : String
j = "j"

jexpr : IntExpr
jexpr = IntVar j

idouble : AnnotatedInst
idouble = A_Assign i (Plus iexpr iexpr)

jdouble : AnnotatedInst
jdouble = A_Assign j (Plus jexpr jexpr)

while : AnnotatedInst
while = A_While (LessThan jexpr iexpr) (BoolAssert (LessThan jexpr iexpr)) (A_Seq idouble jdouble)


doubleLte : {a : Nat} -> {b : Nat} -> (LTE a b) -> (LTE (a+a) (b+b))
doubleLte {a = (S _)} {b = Z} _ impossible
doubleLte {a = Z} {b = b} LTEZero = LTEZero
doubleLte {a = (S i)} {b = (S j)} (LTESucc x) = LTESucc (rewrite (plusCommutative j (S j)) in (rewrite (plusCommutative i (S i)) in ((LTESucc (doubleLte x)))))

doubleLt : {a : Nat} -> {b : Nat} -> (LT a b) -> (LT (a+a) (b+b))
doubleLt {a = _} {b = Z} _ impossible
doubleLt {a = Z} {b = (S _)} _ = LTESucc LTEZero
doubleLt {a = (S i)} {b = (S j)} (LTESucc x) = LTESucc (rewrite (plusCommutative j (S j)) in (rewrite (plusCommutative i (S i)) in (LTESucc (doubleLt x))))

invariantProof : (map : String -> Nat) -> (LTE (S (map "j")) (map "i"), LTE (S (map "j")) (map "i")) -> LTE (S (plus (map "j") (map "j"))) (plus (map "i") (map "i"))
invariantProof map (a, b) = doubleLt a

postConditionProof : (map : String -> Nat) -> (LTE (S (map "j")) (map "i") -> Void, LTE (S (map "j")) (map "i")) -> Void
postConditionProof _ (a, b) = a b

proofOfWhile : valid language.simplePredVal (verificationCondition sumWhile.while FalseAssert)
proofOfWhile = (invariantProof, postConditionProof, ())
