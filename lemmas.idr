module lemmas

%default total
%access public export

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


doubleLte : {a : Nat} -> {b : Nat} -> (LTE a b) -> (LTE (a+a) (b+b))
doubleLte {a = (S _)} {b = Z} _ impossible
doubleLte {a = Z} {b = b} LTEZero = LTEZero
doubleLte {a = (S i)} {b = (S j)} (LTESucc x) = LTESucc (rewrite (plusCommutative j (S j)) in (rewrite (plusCommutative i (S i)) in ((LTESucc (doubleLte x)))))

doubleLt : {a : Nat} -> {b : Nat} -> (LT a b) -> (LT (a+a) (b+b))
doubleLt {a = _} {b = Z} _ impossible
doubleLt {a = Z} {b = (S _)} _ = LTESucc LTEZero
doubleLt {a = (S i)} {b = (S j)} (LTESucc x) = LTESucc (rewrite (plusCommutative j (S j)) in (rewrite (plusCommutative i (S i)) in (LTESucc (doubleLt x))))

ltImpliesNotEq: {a : Nat} -> {b : Nat} -> (LT a b) -> (a = b) -> Void
ltImpliesNotEq {a=Z}{b=Z} aLTb aEqb = void (succNotLTEzero aLTb)
ltImpliesNotEq {a=Z}{b=(S k)} aLTb aEqb = void (SIsNotZ (sym aEqb))
ltImpliesNotEq {a=(S k)}{b=Z} aLTb aEqb = void (SIsNotZ aEqb)
ltImpliesNotEq {a=(S k)}{b=(S j)} aLTb aEqb = ltImpliesNotEq (fromLteSucc aLTb) (succInjective k j aEqb)


multMinus : (mult ac d = a) -> (mult bc d = b) -> (mult (minus ac bc) d = (minus a b))
multMinus {ac=ac} {d=d} {a=a} {bc=bc} {b=b} aDiv bDiv = rewrite (multDistributesOverMinusLeft ac bc d) in (rewrite aDiv in (rewrite bDiv in Refl))

plusMinusEqLeft: (bLTEa : (LTE b a)) -> plus (minus a b) b = a
plusMinusEqLeft bLTa {a=Z} {b=Z} = Refl
plusMinusEqLeft bLTa {a=Z} {b=(S j)} impossible
plusMinusEqLeft bLTa {a=(S k)} {b=Z} = rewrite (plusCommutative k Z) in Refl
plusMinusEqLeft bLTa {a=(S k)} {b=(S j)} =
  rewrite (plusCommutative (minus k j) (S j)) in
    (rewrite (plusCommutative j (minus k j)) in
      (rewrite (plusMinusEqLeft {a=k}{b=j} (fromLteSucc bLTa)) in Refl))

plusMinusEqRight: (aLTEb : (LTE a b)) -> plus a (minus b a) = b
plusMinusEqRight {a=a}{b=b} aLTb = rewrite (plusCommutative a (minus b a)) in (plusMinusEqLeft aLTb)

succInjectiveNotEq : (((S k) = (S j)) -> Void) -> (k = j) -> Void
succInjectiveNotEq {k=k}{j=j} contra prf = contra (eqSucc k j prf)

notEqSucc : ((k = j) -> Void) -> ((S k) = (S j)) -> Void
notEqSucc {k=k}{j=j} contra prf = contra (succInjective k j prf)

notNotEq: {a:Nat} -> {b:Nat} -> Not (Not (a=b)) -> a=b
notNotEq {a=Z} {b=Z} x = Refl
notNotEq {a=(S k)} {b=Z} x = void (x (SIsNotZ))
notNotEq {a=Z} {b=(S k)} x = void (x (negEqSym SIsNotZ))
notNotEq {a=(S k)}{b=(S j)} x = eqSucc k j (notNotEq (\contra => (x (notEqSucc contra))))

multipleLarger: {a: Nat} -> {b : Nat} -> {x : Nat} -> (LT (S a) b) -> (mult x b = (S a)) -> Void
multipleLarger {a=a} {b=Z} {x=x} aSLTb prf = void (succNotLTEzero aSLTb)
multipleLarger {a=a} {b=b} {x=Z} _ prf = void (SIsNotZ (sym prf))
multipleLarger {a=a} {b=b} {x=(S k)} aSLTb prf = ltImpliesNotEq (ltePlusRight aSLTb) (sym prf)
