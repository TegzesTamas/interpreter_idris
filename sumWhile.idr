module sumWhile

import language
import lemmas

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

invariantProof : (map : String -> Nat) -> (LTE (S (map "j")) (map "i"), LTE (S (map "j")) (map "i")) -> LTE (S (plus (map "j") (map "j"))) (plus (map "i") (map "i"))
invariantProof map (a, b) = doubleLt a

postConditionProof : (map : String -> Nat) -> (LTE (S (map "j")) (map "i") -> Void, LTE (S (map "j")) (map "i")) -> Void
postConditionProof _ (a, b) = a b

proofOfWhile : valid language.simplePredVal (verificationCondition sumWhile.while FalseAssert)
proofOfWhile = (invariantProof, postConditionProof, ())
