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


multMinus : (mult ac d = a) -> (mult bc d = b) -> (mult (minus ac bc) d = (minus a b))
multMinus {ac=ac} {d=d} {a=a} {bc=bc} {b=b} aDiv bDiv = rewrite (multDistributesOverMinusLeft ac bc d) in (rewrite aDiv in (rewrite bDiv in Refl))
