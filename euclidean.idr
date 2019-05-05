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

gcdUnchangedLeftMinus : (bLTa : (LT b a)) ->
  (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a b _gcd)))
  -> (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider (minus a b) b _gcd)))
gcdUnchangedLeftMinus bLTa (div ** ((xDiv, yDiv, xyNoLargerDiv),((aC ** aDiv), (bC ** bDiv), abNoLargerDiv)))
  = (div ** ((xDiv, yDiv, xyNoLargerDiv), ((minus aC bC) ** (multMinus aDiv bDiv)), (bC ** bDiv),
  (\(ldLTdiv, (mc**mDiv), (lbc**lbDiv)) => abNoLargerDiv (ldLTdiv, ((mc + lbc) ** (rewrite (multDistributesOverPlusLeft mc lbc largerDiv2) in (rewrite mDiv in (rewrite lbDiv in (plusMinusEqLeft (lteSuccLeft bLTa)))))), (lbc**lbDiv)))))


gcdUnchangedRightMinus : (aLTEb : (LTE a b)) ->
  (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a b _gcd)))
  -> (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a (minus b a) _gcd)))
gcdUnchangedRightMinus aLTb (div ** ((xDiv, yDiv, xyNoLargerDiv),((aC ** aDiv), (bC ** bDiv), abNoLargerDiv)))
  = (div ** ((xDiv, yDiv, xyNoLargerDiv),(aC ** aDiv), ((minus bC aC) ** (multMinus bDiv aDiv)),
  (\(ldLTdiv, (lac**laDiv), (mc**mDiv)) => abNoLargerDiv (ldLTdiv,(lac**laDiv), ((lac + mc) ** (rewrite (multDistributesOverPlusLeft lac mc largerDiv2) in (rewrite mDiv in (rewrite laDiv in (plusMinusEqRight aLTb)))))))))


invariantProof : {a: Nat} -> {b : Nat} -> {x : Nat} -> {y : Nat}->
  ((a=b -> Void), (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a b _gcd)))) ->
  Either
    ((LT b a), (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider (minus a b) b _gcd))))
    (((LT b a) -> Void) , (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a (minus b a) _gcd))))
invariantProof {a=a}{b=b}{x=x}{y=y} (_, preInvariant) with (isLTE (S b) a)
  invariantProof (_, preInvariant) | (Yes prf) = Left (prf , gcdUnchangedLeftMinus prf preInvariant)
  invariantProof (_, preInvariant) | (No contra) = Right (contra, gcdUnchangedRightMinus (notLTImpliesGTE contra) preInvariant)


euclideanProof : valid language.simplePredVal (verificationCondition euclidean.program euclidean.postCondition)
euclideanProof = (?xy, ?yz, ())
