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
invariant = ?invar

while : AnnotatedInst
while = A_While aNotEqB invariant whileBody

postCondition : Assertion
postCondition = AndAssert (BoolAssert (Divides aExpr yExpr)) (BoolAssert (Divides aExpr xExpr))


euclideanProof : valid language.simplePredVal (verificationCondition program euclidean.postCondition)
