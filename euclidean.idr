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
postCondition = GCD xExpr yExpr aExpr

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

sameNumberGcdSelf: {a: Nat} -> {b : Nat} -> {gcd : Nat} -> (a=b) -> (greatestCommonDivider a b gcd) -> (gcd=a)
sameNumberGcdSelf {a=a}{b=b}{gcd=gcd} prf ((ac ** aDiv), (bc ** bDiv), noLargerDiv) with (cmp a gcd)
  sameNumberGcdSelf {a=a}{b=b}{gcd=(a + (S y))} prf ((ac ** aDiv), (bc ** bDiv), noLargerDiv)         | (CmpLT y) with (isItSucc a)
    sameNumberGcdSelf {a=Z}{b=b}{gcd=((S y))} prf ((ac ** aDiv), (bc ** bDiv), noLargerDiv)           | (CmpLT y)      | (No contra) = void (noLargerDiv ((ltePlusLeft {z=1} lteRefl), (0 ** multZeroLeftZero (S (S (S y)))), (0 ** rewrite (sym prf) in (multZeroLeftZero (S (S (S y)))))))
    sameNumberGcdSelf {a=(S a)}{b=b}{gcd=((S a)+(S y))} prf ((ac ** aDiv), (bc ** bDiv), noLargerDiv) | (CmpLT y)      | (Yes aIsSucc) = void (multipleLarger {a=a} {b=(plus (S a) (S y))} (rewrite (plusCommutative a (S y)) in (rewrite (plusCommutative y a) in (lteAddRight (S (S a))))) aDiv)
  sameNumberGcdSelf {a=a}{b=b}{gcd=a} prf ((ac ** aDiv), (bc ** bDiv), noLargerDiv)                   | (CmpEQ)  = Refl
  sameNumberGcdSelf {a=(gcd + (S x))}{b=b}{gcd=gcd} prf ((ac ** aDiv), (bc ** bDiv), noLargerDiv)     | (CmpGT x)  = void (noLargerDiv ((ltePlusRight {z=(x)} lteRefl),
    (1 ** (rewrite (plusCommutative (plus gcd x) Z) in (plusSuccRightSucc gcd x))),
    (1 ** (rewrite (plusCommutative (plus gcd x) Z) in rewrite (plusSuccRightSucc gcd x) in (prf)))
  ))

postConditionProof: {a: Nat} -> {b : Nat} -> {x : Nat} -> {y : Nat}->
  ((Not(Not(a=b))), (_gcd : Nat ** ((greatestCommonDivider x y _gcd), (greatestCommonDivider a b _gcd)))) -> (greatestCommonDivider x y a)
postConditionProof {a=a}{b=b}{x=x}{y=y} (aNotNotEqb, (_gcd ** (gcdXY, (gcdAB)))) = (rewrite (sym (sameNumberGcdSelf aEqb gcdAB)) in (gcdXY)) where
  aEqb : a = b
  aEqb = notNotEq aNotNotEqb

euclideanProof : valid language.simplePredVal (verificationCondition euclidean.program euclidean.postCondition)
euclideanProof = (\map => invariantProof, \map => postConditionProof, ())
