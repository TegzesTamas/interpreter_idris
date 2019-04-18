module example_program

import language

%default total

x : IntExpr
x = IntVar "x"

xplusplus : AnnotatedInst
xplusplus = A_Assign "x" (Plus (IntLiteral 1) x)

plusplusx : AnnotatedInst
plusplusx = A_Assign "x" (Plus x (IntLiteral 1))

xLessThan3 : Assertion
xLessThan3 = BoolAssert (LessThan x (IntLiteral 3))

xLessThan4 : Assertion
xLessThan4 = BoolAssert (LessThan x (IntLiteral 4))

assertXplusplus : AnnotatedInst
assertXplusplus = Pre xLessThan3 xplusplus

assertPlusplusX : AnnotatedInst
assertPlusplusX = Pre xLessThan3 plusplusx

simpleProof : (map : String -> Nat) -> LT (map varName) 3 -> LT (1 + (map varName)) 4
simpleProof map prf = LTESucc prf

proofReq : valid language.simplePredVal (language.verificationCondition example_program.assertXplusplus example_program.xLessThan4)
proofReq = (simpleProof, ())


plusCommutativeLTRight : {a : Nat} -> {b : Nat} -> {x : Nat} -> LT x (a+b) -> LT x (b+a)
plusCommutativeLTRight {a} {b} {x} prf = rewrite (plusCommutative b a) in prf

plusCommutativeLTLeft : LT (a+b) x -> LT (b+a) x
plusCommutativeLTLeft {a} {b} {x} prf = rewrite (plusCommutative b a) in prf

compProof : (map : String -> Nat) -> LT (map varName) 3 -> LT ((map varName) + 1) 4
compProof map prf = plusCommutativeLTLeft(LTESucc prf)

proofOtherReq : valid language.simplePredVal (language.verificationCondition example_program.assertPlusplusX example_program.xLessThan4)
proofOtherReq = (compProof, ())
