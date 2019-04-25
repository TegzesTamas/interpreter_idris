module sumToHundred

import language

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

xLteSx : {x : Nat} -> (LTE x (S x))
xLteSx {x = Z} = LTEZero
xLteSx {x = (S k)} = LTESucc xLteSx

xLteNatPlusX : {x : Nat} -> {y : Nat} -> (LTE x (y+x))
xLteNatPlusX {y = Z} = lteRefl
xLteNatPlusX {y = (S k)} = lteTransitive xLteNatPlusX xLteSx

xLteXPlusNat : {x : Nat} -> {y : Nat} -> (LTE x (x+y))
xLteXPlusNat {x=x} {y=y} = rewrite (plusCommutative x y) in xLteNatPlusX

ltePlusRight : (LTE x y) -> (LTE x (y+z))
ltePlusRight x = lteTransitive x xLteXPlusNat

ltePlusLeft : (LTE x y) -> (LTE x (z+y))
ltePlusLeft {z=z} {y=y} prf = rewrite (plusCommutative z y) in (ltePlusRight prf)

ltePlus : {x : Nat} -> {y : Nat} -> {a : Nat} -> {b : Nat} -> (LTE x y) -> (LTE a b) -> (LTE (x+a) (y+b))
ltePlus {x = Z} _ alteb = ltePlusLeft alteb
ltePlus {y = Z} {x = Z} _ alteb = alteb
ltePlus {y = Z} {x = (S k)} _ _ impossible
ltePlus {a = Z} {x = x} xltey _ = rewrite (plusCommutative x Z) in (lteTransitive xltey xLteXPlusNat)
ltePlus {b = Z} {a = Z} {x = x} {y = y} xltey _ = rewrite (plusCommutative x Z) in (rewrite (plusCommutative y Z) in xltey)
ltePlus {b = Z} {a = (S k)} _ _ impossible
ltePlus {x = (S i)} {y= (S j)} {a = (S k)} {b = (S l)} (LTESucc iltej) (LTESucc kltel) =
  LTESucc ( rewrite (plusCommutative i (S k)) in (rewrite (plusCommutative j (S l)) in
  (LTESucc (rewrite (plusCommutative k i) in (rewrite (plusCommutative l j) in (ltePlus iltej kltel))))))

postconditionPrf : (map : String -> Nat) -> (LTE (S (map "i")) 100 -> Void, LTE (S (map "i")) (map "sum"), LTE 1 (map "i")) -> LTE (S (map "i")) (map "sum")
postconditionPrf map (_, (prf,_)) = prf

invariantPrf : (map : String -> Nat) -> (LTE (S (map "i")) 100, LTE (S (map "i")) (map "sum"), LTE 1 (map "i")) -> (LTE (S (plus (map "i") 1)) (plus (map "sum") (map "i")), LTE 1 (plus (map "i") 1))
invariantPrf map (a, (b,c)) = ((ltePlus b c), (lteTransitive c xLteXPlusNat))

prfOfProgram : valid language.simplePredVal (verificationCondition sumToHundred.program sumToHundred.postCondition)
prfOfProgram = (invariantPrf, postconditionPrf, ())
