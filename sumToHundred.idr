module sumToHundred

import language
import lemmas

%default total

sum : IntExpr
sum = IntVar "sum"

i : IntExpr
i = IntVar "i"

-- i = 1
ieq1 : AnnotatedInst
ieq1 = A_Assign "i" (IntLiteral 1)

-- sum = 0
sumeq2 : AnnotatedInst
sumeq2 = A_Assign "sum" (IntLiteral 2)

-- sum = sum + i
sumeqsumplusi : AnnotatedInst
sumeqsumplusi = A_Assign "sum" (Plus sum i)

iplusplus : AnnotatedInst
iplusplus = A_Assign "i" (Plus i (IntLiteral 1))

whileBody : AnnotatedInst
whileBody = A_Seq sumeqsumplusi iplusplus

iLessThan100 : BoolExpr
iLessThan100 = LessThan i (IntLiteral 100)

invariant : Assertion
invariant = AndAssert (BoolAssert (LessThan i sum)) (BoolAssert (LessThan (IntLiteral 0) i))

while : AnnotatedInst
while = A_While iLessThan100 invariant whileBody

program : AnnotatedInst
program = A_Seq (A_Seq ieq1 sumeq2)(while)

postCondition : Assertion
postCondition = BoolAssert(LessThan i sum)


postconditionPrf : (map : String -> Nat) -> (LTE (S (map "i")) 100 -> Void, LTE (S (map "i")) (map "sum"), LTE 1 (map "i")) -> LTE (S (map "i")) (map "sum")
postconditionPrf map (_, (prf,_)) = prf

invariantPrf : (map : String -> Nat) -> (LTE (S (map "i")) 100, LTE (S (map "i")) (map "sum"), LTE 1 (map "i")) -> (LTE (S (plus (map "i") 1)) (plus (map "sum") (map "i")), LTE 1 (plus (map "i") 1))
invariantPrf map (a, (b,c)) = ((ltePlus b c), (lteTransitive c xLteXPlusNat))

prfOfProgram : valid language.simplePredVal (verificationCondition sumToHundred.program sumToHundred.postCondition)
prfOfProgram = (invariantPrf, postconditionPrf, ())
