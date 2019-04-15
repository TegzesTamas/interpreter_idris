module example_program

import language

x : IntExpr
x = IntVar "x"

xplusplus : AnnotatedInst
xplusplus = A_Assign "x" (Plus (IntLiteral 1) x)

xLessThan3 : Assertion
xLessThan3 = BoolAssert (LessThan x (IntLiteral 3))

xLessThan4 : Assertion
xLessThan4 = BoolAssert (LessThan x (IntLiteral 4))

assertXplusplus : AnnotatedInst
assertXplusplus = Pre xLessThan3 xplusplus

simpleProof : (map : String -> Nat) -> LT (map "x") 3 -> LT (1 + (map "x")) 4
simpleProof map prf = LTESucc prf

proofReq : valid language.simplePredVal (language.verificationCondition example_program.assertXplusplus example_program.xLessThan4)
proofReq = (simpleProof, ())
