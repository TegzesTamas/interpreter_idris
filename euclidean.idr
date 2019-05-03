module euclidean

import language
import lemmas

%default total

x : String
x = "x"

xExpr : IntExpr
xExpr = IntVar x

y : String
y = "y"

yExpr : IntExpr
yExpr = IntVar y

a : String
a = "a"

aExpr : IntExpr
aExpr = IntVar a

b : String
b = "b"

bExpr : IntExpr
bExpr = IntVar b

aEqX : AnnotatedInst
aEqX = A_Assign a xExpr

bEqY : AnnotatedInst
bEqY = A_Assign b yExpr

aNotEqB : BoolExpr
aNotEqB = Neg (Equals aExpr bExpr)

bLessThanA : BoolExpr
bLessThanA = LessThan bExpr aExpr

aMinusEqB : AnnotatedInst
aMinusEqB = A_Assign a (Minus aExpr bExpr)

bMinusEqA : AnnotatedInst
bMinusEqA = A_Assign b (Minus bExpr aExpr)

whileBody : AnnotatedInst
whileBody = A_If bLessThanA aMinusEqB bMinusEqA

invariant : Assertion
invariant = GCDEQ xExpr yExpr aExpr bExpr

while : AnnotatedInst
while = A_While aNotEqB invariant whileBody

postCondition : Assertion
postCondition = AndAssert (BoolAssert (Divides aExpr yExpr)) (BoolAssert (Divides aExpr xExpr))

program : AnnotatedInst
program = A_Seq (A_Seq aEqX bEqY) while

gcdUnchangedLeftMinus :{prf : (LT b a)} -> (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a b _gcd))) -> (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider ((-) a b {smaller=(lteSuccLeft prf)}) b _gcd)))
gcdUnchangedLeftMinus (div ** ((xDiv, yDiv, xyNoLargerDiv),((aC ** aDiv), (bC ** bDiv), abNoLargerDiv))) = (div ** ((xDiv, yDiv, xyNoLargerDiv), ((minus aC bC) ** (multMinus aDiv bDiv)), (bC ** bDiv), ?aMinusBBNoLargerDiv))

invariantProof : {a: Nat} -> {b : Nat} -> {x : Nat} -> {y : Nat}->
  ((a=b -> Void), (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a b _gcd)))) ->
  Either
    (prf : (LT b a) ** (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider ((-) a b {smaller=(lteSuccLeft prf)}) b _gcd))))
    (prf : ((LT b a) -> Void) ** (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a ((-) b a {smaller=notLTImpliesGTE prf}) _gcd))))
invariantProof {a=a}{b=b}{x=x}{y=y} (_, preInvariant) with (isLTE (S b) a)
  invariantProof (_, preInvariant) | (Yes prf) = Left (prf ** gcdUnchangedLeftMinus {prf=prf} preInvariant)
  invariantProof (_, preInvariant) | (No contra) = Right (contra ** ?b)


euclideanProof : valid language.simplePredVal (verificationCondition euclidean.program euclidean.postCondition)
euclideanProof = (?euclideanProof_rhs1, ?euclideanProof_rhs2, ())
