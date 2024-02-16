module Unitary

import Data.Vect
import Data.Nat
import Data.Maybe
import System.File
import Injection
import Lemmas

infixr 9 .
infixr 10 #

%default total


-------------------------------LEMMAS--------------------------

export
comeOnIdrisMinusZero : (n:Nat) -> {auto prf: LTE Z n}  -> (minus n 0) = n
comeOnIdrisMinusZero Z =  Refl
comeOnIdrisMinusZero (S m) = minusZeroRight (S m)
 
export
comeOnIdrisMinus : (n:Nat) -> {auto prf: LTE Z n}  -> (minus (S n) 1) = n
comeOnIdrisMinus Z = Refl
comeOnIdrisMinus n = comeOnIdrisMinusZero n {prf}

export
comeOnIdrisAux : (m:Nat) -> (prf : LTE 1 (S m)) -> LTE 0 m
comeOnIdrisAux Z prf = LTEZero
comeOnIdrisAux (S m) prf =  fromLteSucc prf

export
singleStep : {n:Nat} -> plus n 1 = S n 
singleStep {n} = (rewrite (plusCommutative n 1) in (replace {x = (plus 1 n) } { y = (S n)} {p = \z => z = S n}  (plusOneSucc n) (Refl)))

--export
--comeOnIdrisPlus : {n:Nat} -> (plus n 1) (S n)
--comeOnIdrisPlus {n} = (replace {x = (plus n 1) } { y = (S n)} {p = (\z => equalNat z (S n))} (singleStep {n}) (?what)) 
  --replace {x = (S n) } { y = (plus 1 n)} {p = \z => equalNat (plus n 1) z = True} (sym (plusOneSucc n)) (replace {x = (plus n 1) } { y = (plus 1 n)} {p = \z => equalNat z (plus 1 n) = True} (plusCommutative n 1) (replace (plusZeroLeftNeutral n) (cong equalNat Refl))) --replace {x = (S n)} { y = (plus 1 n) } {p = \z => equalNat (plus n 1) z = True} (sym (plusOneSucc (n))) (replace {x = (plus 1 n)} { y = (plus n 1) } {p = \f => equalNat (plus n 1) f = True} (plusCommutative 1 n) (Refl)) --{(Refl)

export
comeOnIdris : (n:Nat) ->  {auto prf: LT Z n} -> plus (minus n 1) 1 = n 
comeOnIdris Z impossible
comeOnIdris (S m) = rewrite (comeOnIdrisMinus {n = m} {prf = comeOnIdrisAux m prf}) in (singleStep {n=m})

export
comeOnIdrisFull : {n:Nat} -> {auto prf: LT Z n} -> (exp:Fin (plus (minus n 1) 1)) -> Fin n
comeOnIdrisFull {n} {prf} exp = rewrite (sym $ comeOnIdris n) in exp

%hint
plusZeroRightNeutralLocal : {m:Nat} -> plus m 0 = m
plusZeroRightNeutralLocal {m} = plusZeroRightNeutral m

%hint
plusZeroRightNeutralLocalSym : {m:Nat} -> m = plus m 0 
plusZeroRightNeutralLocalSym {m} = sym $ plusZeroRightNeutral m


---- Proofs exist, but take a while, saved for later ----
export
comeOnIdrisGenPre : {n:Nat} -> (m:Nat) -> {auto prf: LTE m n } -> plus m (minus n m) = minus (plus m n) m
comeOnIdrisGenPre Z = Refl
comeOnIdrisGenPre (S n) = ?justnope --WAY too long. Saw the end, so I will return  
                      --replace {x = (plus m (S n)) } {y = (plus (S n) m)} {p = (\x => plus m (minus (S n) m) = minus x (S n))} (plusCommutative m (S n))
                        --(replace {x = (S n) } {y = plus (S n) 0} {p = (\x => plus m (minus (S n) m) = minus (plus (S n) m) x)} (sym $ plusZeroRightNeutral (S n))
                            --(replace {x =  minus (plus n m) (plus n 0 ) } {y = minus m 0 } {p = (\x => plus m (minus (S n) m) = x)} (plusMinusLeftCancel n m 0 )  ?what42))
export                           
comeOnIdrisGenPre2 : {n:Nat} -> {m:Nat} -> {auto prf: LTE m n } -> minus (plus m n) m = n
comeOnIdrisGenPre2 {n} {m} {prf} =  ?justnope2 --WAY too long. Saw the end, so I will return
                        --(replace {x = m } {y = plus m 0} {p = (\x => minus (plus m n) x = n)} (sym $ plusZeroRightNeutral m) (rewrite (sym $ plusZeroRightNeutral m) in (replace {p = \x  => x = n} (sym $ plusMinusLeftCancel m n Z) (rewrite (minusZeroRight n) in Refl))))
---------------------------------------------------------

export
%hint
comeOnIdrisGen : {n:Nat} -> {m:Nat} ->  {auto prf: LTE m n } -> plus m (minus n m) = n
--comeOnIdrisGen {n} Z {prf} = replace {x = plus Z (minus n Z)} {y = minus (plus Z n) Z} {p = (\x => x = n)} (comeOnIdrisGenPre Z {n = n} {prf = prf}) (rewrite (minusZeroRight n) in (Refl))
comeOnIdrisGen {n} {m} {prf} = rewrite (comeOnIdrisGenPre {n = n} m {prf = prf}) in (rewrite (comeOnIdrisGenPre2 {n = n} {m = m} {prf = prf}) in Refl)
export
||| copy of new library function `LTE` is transitive
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)

export
||| explicit version of lte reflexivity because idris is confused easily
lteReflExpl : (n:Nat) -> LTE n n
lteReflExpl Z  = LTEZero
lteReflExpl (S k) = LTESucc (lteReflExpl k)


export
%hint
lteTransOne : {n,p:Nat} -> (prf1: LTE 1 p) -> (prf2: LTE 1 n) -> LTE 1 (plus n p)
lteTransOne prf1 prf2 = lteTransitive prf2 (lteAddRight n)

export
subst : {A : Type} -> {x, y : A} -> (B : A -> Type) -> x = y -> B x -> B y
subst _ Refl bx = bx

private
fs : {n, k : Nat} -> S n = S k -> n = k
fs {n} {k} eq = ?

private 
disjoint : (n : Nat) -> Prelude.Z = S n -> Void
disjoint n prf = replace {p = disjointTy} prf ()
  where
    disjointTy : Nat -> Type
    disjointTy Prelude.Z = ()
    disjointTy (S k) = Void

export
isDifferentFin : Fin m -> Vect n (Fin m)-> Bool
isDifferentFin n [] = True
isDifferentFin n (x :: xs) = (n /= x) && isDifferentFin n xs

export
isDifferentFinImpl : {n :Nat} -> Fin m -> Vect n (Fin m)-> Bool
isDifferentFinImpl n [] = True
isDifferentFinImpl n (x :: xs) = (n /= x) && isDifferentFinImpl n xs


export
isDifferentFinFin' : {n:Nat} -> (i: Fin n) -> Fin n -> Vect (finToNat i) (Fin n)-> Bool
isDifferentFinFin' FZ n Nil = True
isDifferentFinFin' FZ (FS m) any = True
isDifferentFinFin' (FS len) any (x :: xs) = (finToNat any /= finToNat x) && isDifferentFin any xs

{-export
isDifferentFinFin : {n:Nat} -> (i: Fin n) -> Fin (finToNat i) -> Vect (finToNat i) (Fin n)-> Bool
isDifferentFinFin FZ _ _ impossible
isDifferentFinFin (FS len) any (x :: xs) = ?h --(finToNat any /= finToNat x) && isDifferentFinFin' len any xs
  -}
export
allDifferentFin : Vect n (Fin m)-> Bool
allDifferentFin [] = True
allDifferentFin (x :: xs) = isDifferentFin x xs && allDifferentFin xs

export 
allSmallerFin : Vect n (Fin m) -> Nat -> Bool
allSmallerFin [] m = True
allSmallerFin (x :: xs) m = ((finToNat x) < m) && allSmallerFin  xs m

export
isInjectiveFin : Nat -> Vect n (Fin m)-> Bool
isInjectiveFin m v = allSmallerFin v m && allDifferentFin v

export
lemmaControlledInjective : (n : Nat) -> (j : Fin n) -> isInjective (S n) [0, S (finToNat j)] = True
lemmaControlledInjective 0 any = absurd any
lemmaControlledInjective (S k) FZ = Refl
lemmaControlledInjective (S p) (FS k) = lemmaControlledInjective p k 

export 
sSinj : (n : Nat) -> (m : Nat) -> (prf: S n < S m = True) -> (n < m = True)
sSinj 0 0 prf = absurd prf
sSinj (S l) 0 prf = absurd prf
sSinj 0 (S k) prf = Refl
sSinj (S l) (S k) prf = sSinj l k prf

export
finFSApp : (n:Nat) -> (k: Fin n) -> finToNat k < n = True
finFSApp 0 any = absurd any
finFSApp (S m) FZ = Refl
finFSApp (S m) (FS l) = finFSApp m l


export
lemmaControlledInjective2 : (n : Nat) -> (c : Fin n) -> (t : Fin n) -> {auto prf : (c /= t) = True} -> isInjectiveFin (S n) [FZ, FS c, FS t] = True
lemmaControlledInjective2 0 any _ = absurd any
lemmaControlledInjective2 (S k) FZ FZ {prf} = prf
lemmaControlledInjective2 (S k) FZ (FS j) {prf} = lemmaAnd (lemmaAnd (finFSApp (S k) (FS j)) Refl) Refl
lemmaControlledInjective2 (S k) (FS j) FZ {prf} = lemmaAnd (lemmaAnd (finFSApp (S k) (FS j)) Refl) Refl
lemmaControlledInjective2 (S k) (FS j) (FS i) {prf} = lemmaControlledInjective2 k j i {prf}

export
finFSapp : (n:Nat) -> (l: Fin n) -> (finToNat (FS l) < S n = True) = (S (finToNat l) < S n = True)
finFSapp 0 any = absurd any
finFSapp (S m) FZ = Refl
finFSapp (S m) (FS k) = Refl

export
pluslengthlemma : (len: Nat) -> plus len 1 = S len
pluslengthlemma m = (plusCommutative m 1)

export
pluslengthlemmaRev : (len: Nat) -> S len = plus len 1
pluslengthlemmaRev m = sym (pluslengthlemma m)

-- Due to structure, has to be used with "nub." Should be rewritten. Bit hacky, but works :D --
export
rangeVectFin : (len:Nat) -> (k : Nat) -> (i : Fin k) -> Vect len (Fin k)
rangeVectFin (S Z) (S k) FZ = [(FZ)]
rangeVectFin Z any i = []
rangeVectFin any Z i impossible
rangeVectFin (S len) (S k) (FZ) = (rewrite (pluslengthlemmaRev len) in (rangeVectFin len (S k) (FZ) ++ [(FZ)]))
rangeVectFin (S len) (S k) (FS i)= rewrite (pluslengthlemmaRev len) in (rangeVectFin len (S k) (weaken i) ++ [(FS i)])


allSmallerRangeVect2 : (startIndex : Nat) -> (length : Nat) -> allSmaller (rangeVect startIndex length) (startIndex + length) = True
allSmallerRangeVect2 startIndex 0 = Refl
allSmallerRangeVect2 0 0 = Refl
allSmallerRangeVect2 0 (S k) = 
  rewrite sym $ plusSuccRightSucc 0 k in 
          lemmaAnd (lemmaLTSuccPlus 0 k) (allSmallerRangeVect2 (S 0) k) 
allSmallerRangeVect2 startIndex (S k) = 
  rewrite sym $ plusSuccRightSucc startIndex k in 
          lemmaAnd (lemmaLTSuccPlus startIndex k) (allSmallerRangeVect2 (S startIndex) k) 


export
allDiffRangeVectFin : (len:Nat) -> (k : Nat) -> (i : Fin k) ->  allDifferentFin (snd (Data.Vect.nub (rangeVectFin len k i))) = True
allDiffRangeVectFin _ _ _ = ?nubdef -- since nub is proven to do what we need it to, we are alright to ignore tis proof

export
%hint
justFinLemma : (n:Nat) -> (k:Nat) -> {auto prf: LTE 1 k} -> Fin (n+k)
justFinLemma any 0 = absurd prf
justFinLemma 0 (S k)= FZ
justFinLemma (S n) k = FS (justFinLemma n k {prf})

export
justFinEq : {k:Nat} -> (justFinLemma 0 (S k) = FZ)
justFinEq = Refl

export
finPlusComm : {n,p:Nat} -> Fin (n+p) = Fin (p+n)
finPlusComm {n} {p}= cong Fin (plusCommutative n p)

export
finToNatFZLemma : finToNat FZ = Z
finToNatFZLemma  = Refl

export
fTNFSLemma : {any: Fin p} -> finToNat (FS any) = S (finToNat any)
fTNFSLemma = Refl

export
jFLFS : {n:Nat} -> {k:Nat} -> {auto prf: LTE 1 k}  ->  (FS (justFinLemma n (k) {prf})) =(justFinLemma (S n) (k) {prf}) 
jFLFS = case k of 
          0 => absurd prf
          S p => Refl

%hint
finToNatJustFin : (n:Nat) -> (k:Nat) -> {auto prf: LTE 1 k} -> (finToNat (justFinLemma n k) = n) 
finToNatJustFin any 0 = absurd prf
finToNatJustFin 0 (S k)= Refl
finToNatJustFin (S n) (S k) = replace {x = (justFinLemma (S n) (S k))} {y = (FS (justFinLemma n (S k)))} {p = \x => finToNat x = S n} (jFLFS {n} {k = (S k)} {prf}) (cong S (finToNatJustFin n (S k)))  --(replace {p = \y => y = S n} (fTNFSLemma {any = (FS (justFinLemma n (S k)))}) Refl)-- in (finToNat (justFinLemma n k))) rewrite (fTNFSLemma {(justFinLemma n (S k))}) in (rewrite 

 
export
ltePlusGTE : {a,b,c:Nat} -> (prf: LTE (a + b) c) -> LTE a c
ltePlusGTE {a} {b} {c} prf =  lteTransitive (lteAddRight a) prf

export
ltePlusGTEright : {a,b,c:Nat} -> (prf: LTE (a + b) c) -> LTE b c
ltePlusGTEright {a} {b} {c} prf =  lteTransitive (lteAddRight b) (replace {p = \x => LTE x c} (plusCommutative a b) prf)

export
--?hint
plusSuccRight: {left,right:Nat} -> plus left (S right) = S (plus left right)
plusSuccRight {left,right} = sym (plusSuccRightSucc left right)

export 
revGTEisLTE : {a,b : Nat} -> GTE a b = LTE b a
revGTEisLTE = Refl

--the following is written in the way it is because idris refused to recognize anything in rewrite or replace. so it had to be done step by step...
export
gteEqisLTEleft : {left,right,gt:Nat} -> {expr: Type} -> (eq: GTE gt (plus left (S right)) = expr) -> LTE (plus left (S right)) gt = expr
gteEqisLTEleft eq = replace {x = GTE gt (plus left (S right))} {y = LTE (plus left (S right)) gt} {p = (\x => x = expr)} revGTEisLTE eq
                  
export
gteEqisLTEright : {left,right,gt:Nat} -> {expr: Type} -> (eq: expr = GTE gt (S (plus left right))) -> expr = LTE (S (plus left right)) gt
gteEqisLTEright eq = (replace {x = GTE gt (S (plus left right))} {y = LTE (S (plus left right)) gt} {p = (\x => expr = x)} revGTEisLTE (eq))

export 
plusSuccRightLTE : {left, right, gt : Nat} -> LTE (plus left (S right)) gt -> LTE (S (plus left right)) gt  
plusSuccRightLTE {left, right, gt} prf = replace {p = (\x => x)} (gteEqisLTEright $ (gteEqisLTEleft {expr = GTE gt (S (plus left right))}) (cong (GTE gt) (plusSuccRight {left = left} {right = right}))) prf

export --this is of cours eabsurd but becasue idris cannot do it itself...
--?hint
lteSLemma : {m,n:Nat} -> (LTE (plus m (S n)) Z) -> (LTE (S n) Z)
lteSLemma {m} {n} prf =  ltePlusGTEright prf
  --ltePlusGTE {a = S n} {b = m} {c = Z} (plusSuccRightLTE {left = m} {right = n} {gt = Z} (prf)) --replace (plusCommutative m (S n )) (ltePlusGTE {a = S n} {b = m} {c = Z} ((plusSuccRightLTE {left = m} {right = n} {gt = Z} prf))) --

export
--?hint
Uninhabited (LTE (plus a (S bb)) Z) where
  uninhabited (LTEZero (plus a (S bb)) Z) impossible

export 
ltToLTE : {left,right:Nat} -> LTE (S left) right = LT left right 
ltToLTE = Refl

export
succPlusSuccSS : {a,b:Nat} -> (S (plus a (S b))) = (S (S (plus a b)))
succPlusSuccSS {a} {b} = replace {p = (\x => (S x) = (S (S (plus a b))))} (plusSuccRightSucc a b) Refl

export --of course the og version is not seen..
lteRefl : (n:Nat) -> LTE n n
lteRefl Z  = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

export
ltePlusGT : (a,b,c:Nat) -> (prf: LTE (a + b) c) -> {auto prfB: LTE 1 b} -> LT a c
ltePlusGT a b Z prf = case b of 
                        Z => absurd prfB 
                        (S bb) => absurd (lteSLemma prf)
ltePlusGT _ Z _ prf impossible
ltePlusGT Z (S b) (S c) prf = lteTransitive prfB  (replace {p = \x => LTE x (S c)} (plusZeroLeftNeutral (S b)) (prf))
ltePlusGT (S a) (S b) (S c) prf = case b of 
  Z => replace {p = (\x => LTE (S x) (S c))} (singleStep {n=a}) prf
  (S bb) => ltePlusGTE (replace {p = (\x => LTE x (S c))} (succPlusSuccSS {a = a} {b = S bb}) (prf))
  --lteTransitive (lteAddRight a) prf


--?hint
mZr : {c:Nat} -> minus c 0 = c
mZr {c} =  minusZeroRight c

export
ifLTplusThenLT : {a,b,c:Nat} ->  (prf: LTE (a + b) c) -> {auto prfB: LTE 1 b} -> LTE 1 (minus c a)
ifLTplusThenLT {a} {b} {c} prf {prfB}= case a of
  Z =>  (replace {p = (\x => LTE 1 x)} (sym$ minusZeroRight c) (lteTransitive prfB prf))-- ?what1--(replace {p = (\x => LTE 1 x)} (minusZeroRight c) ((replace (minusZeroRight c) (ltePlusGT a b c prf))))
  S aa => ?timeconsumingbuteasy

export
assertZero : (assert_total (integerToNat 0)) = 0
assertZero = Refl

export --(rewrite (plusSuccRightSucc (assert_total (integerToNat 0)) j) in
lteOneMinus : {j,n:Nat} -> LTE (S j) n -> LTE 1 (minus n j)
lteOneMinus prf = ifLTplusThenLT (replace {x = S j} {y = plus j 1} {p = \x => LTE x n} ((pluslengthlemmaRev j)) prf) {prfB =lteRefl 1}


rangeVectAuxLemmaExact : {i,k: Nat} -> {auto prf: LTE i k} -> Fin (plus i (minus k i)) -> Fin k
rangeVectAuxLemmaExact {i} {k} {prf} prfMain = replace {p = \x => Fin x} (comeOnIdrisGen {n=k} {m=i} {prf = prf}) prfMain

export
rangeVectFin' : (startIndex : Nat) -> (length : Nat) -> (finNat : Nat) -> {prf: LTE (startIndex+length) finNat} -> Vect length (Fin finNat)
rangeVectFin' i Z k = []
rangeVectFin' i (S l) k = (rangeVectAuxLemmaExact {k=k} {i=i} {prf = lteSuccLeft (ltePlusGT i (S l) k prf)}) (justFinLemma i (minus k i) {prf =  (ifLTplusThenLT {a = i} {b = (S l)} {c = k} {prf = prf})}) :: rangeVectFin' (S i) l k

export
rangeVectFinNatEq : {length, finNat : Nat} -> Vect length (Fin finNat) -> Vect length Nat
rangeVectFinNatEq [] = []
rangeVectFinNatEq (x::xs) = finToNat x :: rangeVectFinNatEq xs

--- Extremely timeconsuming, but all subproofs accomplished ---
export
isDiffRangeVectFin : {big : Nat} -> (k : Fin big) -> (length : Nat) -> (p : Nat) -> {prf : LTE ((S (p + (finToNat k))) + length) big} -> isDifferentFin k (rangeVectFin' (S (p + (finToNat k))) length big {prf = prf}) = True
isDiffRangeVectFin k 0 _ = Refl
isDiffRangeVectFin k (S j) p = 
lemmaAnd (?timeconsuming) (isDiffRangeVectFin k j (S p)) 

transformedEquivalenceLemma : {finNat, startIndex : Nat} -> {auto prf1: LTE startIndex finNat} -> {auto prf2: LTE 1 (minus finNat startIndex)} -> startIndex = finToNat (rangeVectAuxLemmaExact {i = startIndex} {k = finNat} (justFinLemma startIndex (minus finNat startIndex)))
transformedEquivalenceLemma {finNat} {startIndex} = ?takestoolong --one of those very doable and obvious but very long proofs... so saved for a colder day, for now.

export
allDiffRangeVectFin' : (startIndex : Nat) -> (length : Nat) -> {finNat : Nat} -> {prf: LTE (startIndex+length) finNat} -> allDifferentFin (rangeVectFin' startIndex length finNat {prf = prf}) = True
allDiffRangeVectFin' startIndex 0  {finNat} = Refl
allDiffRangeVectFin' startIndex (S k) {finNat} = 
  let p1 = isDiffRangeVectFin (justFinLemma startIndex (minus finNat startIndex) {prf = ?easyfromabovebuttime}) k 0
  in ?easyfromabovebuttimeusebelowcomment (lemmaAnd p1 (allDiffRangeVectFin' (S startIndex) k {finNat = finNat} {prf = rewrite (plusSuccRightSucc startIndex k) in prf}))
  --(rewrite (sym $ comeOnIdrisGen {n = finNat} {m = startIndex} {prf = ltePlusGTE prf}) in 



export --proofs for this are accomplished below, but takes a long time to put together
differentIndexInjectiveVectFin : (n: Nat) -> (i: Fin n) -> (c : Fin (finToNat i)) -> (t : Fin (finToNat i)) -> 
                              (v : Vect (finToNat i) (Fin n)) -> {prf : allDifferentFin v = True} -> (prf3: Either (LT (finToNat c) (finToNat t)) (LT (finToNat t) (finToNat c)))->
                              (Either (LT (finToNat (index c v)) (finToNat (index t v))) (LT (finToNat (index t v)) (finToNat (index c v))))
differentIndexInjectiveVectFin 0 any _ _ _  _ = absurd any
differentIndexInjectiveVectFin (S k) FZ _ _  prf2 prf3 impossible
differentIndexInjectiveVectFin (S k) (FS l) FZ (Z) v {prf2} prf3 impossible
differentIndexInjectiveVectFin (S k) (FS l) FZ (FS t) v {prf} prf3 = ?h2
differentIndexInjectiveVectFin (S k) (FS l) (FS c) (FZ) v {prf} prf3 = ?h3
differentIndexInjectiveVectFin (S k) (FS l) (FS c) (FS t) v {prf} prf3 = ?h4

{-}
export
differentIndexInjectiveVect : (n: Nat) -> (i: Fin n) -> (c : Fin (finToNat i)) -> (t : Fin (finToNat i)) -> 
                              (v : Vect (finToNat i) Nat) -> {prf : allDifferentFin v = True} ->
                              {prf3 : c < i = True} -> {prf4 : t < i = True} ->
                              (prf2: index c v = index t v)-> Void
differentIndexInjectiveVect 0 (S m) n (x :: xs) =
      different' x m xs {prf1 = prf4} {prf2 = lemmaAndLeft (lemmaAndRight prf2)}
differentIndexInjectiveVect (S k) 0 n (x :: xs) =
      different'' x k xs {prf1 = prf3} {prf2 = lemmaAndLeft (lemmaAndRight prf2)}
differentIndexInjectiveVect (S k) (S j) n (x :: xs) =
  let p2 = lemmaAnd (lemmaAndRight (lemmaAndLeft prf2)) (lemmaAndRight (lemmaAndRight prf2)) in
  differentIndexInjectiveVect k j n {prf1} xs {prf2 = p2} {prf3} {prf4}
-}

------------------------QUANTUM CIRCUITS-----------------------

public export
data Unitary : Nat -> Type where
  IdGate : Unitary n
  H      : (j : Fin n) -> Unitary n -> Unitary n
  P      : (p : Double) -> (j : Fin n) -> Unitary n -> Unitary n
  CNOT   : (c : Fin n) -> (t : Fin n) -> 
            {auto prf3 : Either (LT (finToNat c) (finToNat t)) (LT (finToNat t) (finToNat c))} -> 
            Unitary n -> Unitary n
{-data Unitary : Nat -> Type where
  IdGate : Unitary n
  H      : (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
  P      : (p : Double) -> (j : Nat) -> {auto prf : (j < n) = True} -> Unitary n -> Unitary n
  CNOT   : (c : Nat) -> (t : Nat) -> 
            {auto prf1 : (c < n) = True} -> {auto prf2 : (t < n) = True} -> {auto prf3 : (c /= t) = True} -> 
            Unitary n -> Unitary n
            -}


-- P p = [[1,0],[0,e^ip]]

-------------------------------APPLY---------------------------
|||Apply a smaller circuit of size i to a bigger one of size n
|||The vector of wires on which we apply the circuit must follow some constraints:
|||All the indices must be smaller than n, and they must be all different
public export
apply : {n : Nat} -> {i : Fin n} -> 
        Unitary (finToNat i) -> Unitary n -> 
        (v : Vect (finToNat i) (Fin n)) -> 
        {auto prf : (allDifferentFin v) = True} ->
        {auto valid : LTE 2 n} -> 
        Unitary n
apply IdGate g2 _ = g2
apply (H j g1) g2 v = 
  H (index j v) (apply g1 g2 v)
apply (P p j g1) g2 v = 
  P p (index j v) (apply g1 g2 v)
apply {n} {i} (CNOT c t {prf3} g1) g2 v = 
  let prfnew= differentIndexInjectiveVectFin n i c t v {prf} prf3
  in CNOT (index c v) (index t v) {prf3 = prfnew} (apply {n} {i} g1 g2 v)

---------------------------COMPOSE-----------------------------
|||Compose 2 circuits of the same size
public export
compose : Unitary n -> Unitary n -> Unitary n
compose IdGate g1 = g1
compose (H j g1) g2 = H j (compose g1 g2)
compose (P p j g1) g2 = P p j (compose g1 g2)
compose (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

public export
(.) : Unitary n -> Unitary n -> Unitary n
(.) = compose

---------------------------ADJOINT-----------------------------
|||Find the adjoint of a circuit
public export
adjoint : Unitary n -> Unitary n
adjoint IdGate = IdGate
adjoint (H j g) = (adjoint g) . (H j IdGate)
adjoint (P p j g) = (adjoint g) . (P (-p) j IdGate)
adjoint (CNOT c t g) = (adjoint g) . (CNOT c t IdGate)

-------IDRIS DOING IDRIS THINGS SO WE WILL BE EXPLICIT---------
export
losingMyMindSoMakingThingsExplicit : {p, n:Nat} -> {prf: LTE 1 n} -> Unitary p -> Unitary (finToNat (justFinLemma p n))
losingMyMindSoMakingThingsExplicit u = rewrite finToNatJustFin p n in u

export
crazy : {p, n:Nat} -> {prf: LTE 1 n} -> Vect p (Fin (plus n p)) -> Vect (finToNat (justFinLemma p n)) (Fin (plus n p))
crazy v = replace {p = \x =>  Vect x (Fin (plus n p))} (sym $ finToNatJustFin p n) v

export
Uninhabited (LTE 1 (S kk) -> Void) where
  uninhabited (LTEZero 1 (S kk)) impossible

export
ltOneZero: (k:Nat) -> (prf: LTE 1 k -> Void) -> k = Z
ltOneZero Z prf = Refl
ltOneZero (S kk) prf = absurd prf

export
ltOneZeroPlus: {k, m:Nat} -> (prf: k = Z) -> m = plus k m 
ltOneZeroPlus {k} {m} prf = rewrite prf in (plusZeroLeftNeutral m)

export
twoIsSSZrewrite : 2 = S (S Z)
twoIsSSZrewrite = Refl

%hint 
plusCommEq : {aa,bb:Nat} -> plus aa bb = plus bb aa
plusCommEq = rewrite plusCommutative aa bb in Refl

%hint 
plusCommEqF : {aa,bb:Nat} -> plus aa bb = True -> plus bb aa = True
plusCommEqF prf = rewrite plusCommutative bb aa in prf

export --this is specific because the general one takes long to prove...(fromLteSucc {m = Z} {n = (aa+bb)} (fromLteSucc {m = S Z} {n = S (aa +bb)}
ltePlusSym : (a,b:Nat) -> LTE 1 a -> LTE 1 b -> LTE (1+1) (a+b)
ltePlusSym Z _ prf1 prf2 = absurd prf1
ltePlusSym _ Z prf1 prf2 = absurd prf2
ltePlusSym (S aa) (S bb) prf1 prf2 = (LTESucc $ (replace {p = \x => LTE 1 (aa + (S bb))} (plusSuccRightSucc aa bb) (rewrite sym $ plusSuccRightSucc aa bb in rewrite plusCommutative aa bb in lteTransitive prf2 (lteAddRight (S bb) {m = aa}))))
                                  
---------------------TENSOR PRODUCT----------------------------
--(snd (Data.Vect.nub (rangeVectFin n n (Data.Vect.head (snd (maybeToVect (natToFin (minus n 1) n))))))) {prf = (allDiffRangeVect Z n)} -- nattofin will always work, because p cannot be zero due to Unitary, so i: Fin (n+p) works. proven
|||Make the tensor product of two circuits
public export
tensor : {n : Nat} -> {p : Nat} -> Unitary n -> Unitary p -> Unitary (n + p)
tensor g1 g2 = case isLTE 1 p of
  Yes prf1 => case isLTE 1 n of
    Yes prf2 => 
      let prop1 = (allDiffRangeVectFin' 0 (n) {finNat = n+p})
          prop2 = (allDiffRangeVectFin' n (p) {finNat = n+p} {prf =  lteRefl (n+p)})
          g' = apply {i = justFinLemma n p} {n =  n + p} (replace {p = Unitary} (sym (finToNatJustFin n p {prf= prf1})) g1) 
                  (IdGate {n = n+p}) ( rewrite ((finToNatJustFin n p {prf= prf1})) in rangeVectFin' 0 n (n+p))
                  {prf =  rewrite ((finToNatJustFin n p {prf= prf1})) in prop1} {valid = ltePlusSym n p prf2 prf1}
        in apply {i = rewrite (sym $ finPlusComm {p=n} {n = p}) in (justFinLemma p n)} {n = n + p} 
                  (losingMyMindSoMakingThingsExplicit {n = n} {p = p} {prf = prf2} g2) g' (crazy {prf = prf2} $ rangeVectFin' n p (n+p) {prf =  lteRefl (n+p)} ) --crazy {prf = prf2} $ 
                  {prf = prop2} {valid = ltePlusSym n p prf2 prf1}
    No prf3 => replace {x = p} {y = n+p} { p = \x => Unitary x} (ltOneZeroPlus {k = n} {m = p} (ltOneZero n prf3)) g2
  No prf4 => replace {x = n} {y = n+p} { p = \x => Unitary x} (rewrite (sym $ plusCommutative p n) in ltOneZeroPlus {k = p} {m = n} (ltOneZero p prf4)) g1

public export
(#) : {n : Nat} -> {p : Nat} -> Unitary n -> Unitary p -> Unitary (n + p)
(#) = tensor

----------------------CLASSICAL GATES--------------------------
public export
HGate : Unitary 1
HGate = H 0 IdGate

public export
PGate : Double -> Unitary 1
PGate r = P r 0 IdGate

public export
CNOTGate : Unitary 2
CNOTGate = CNOT FZ (FS FZ) IdGate

pGenerator : {n:Nat} -> (j : Nat) -> (prf : LT j n) -> (rotation : Double) -> Unitary n -> Unitary n
pGenerator {n} j prf r g =  rewrite (sym $ comeOnIdrisGen {n=n} {m=j} {prf = lteSuccLeft prf}) in (P (r) (justFinLemma j (minus n j) {prf = lteOneMinus prf}) (rewrite comeOnIdrisGen {n=n} {m=j} {prf = lteSuccLeft prf} in g)) --rewrite ( sym $ ltToLTE {left =j} {right = n}) in

public export
T : {n:Nat} -> (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
T {n} j g = pGenerator {n = n} j prf (pi/4) g

public export
TGate : Unitary 1
TGate = T 0 IdGate

public export
TAdj : {n:Nat} ->  (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
TAdj {n} j g = pGenerator {n = n} j prf (-pi/4) g

public export
TAdjGate : Unitary 1
TAdjGate = TAdj 0 IdGate

public export
S : {n:Nat} -> (j : Nat) -> {auto prf : LT j n}-> Unitary n -> Unitary n
S {n} j g = pGenerator {n = n} j prf (pi/2) g

public export
SGate : Unitary 1
SGate = S 0 IdGate

public export
SAdj : {n:Nat} -> (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
SAdj {n} j g = pGenerator {n = n} j prf (-pi/2) g

public export
SAdjGate : Unitary 1
SAdjGate = SAdj 0 IdGate

public export
Z : {n:Nat} -> (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
Z {n} j g = pGenerator {n = n} j prf (pi) g

public export
ZGate : Unitary 1
ZGate = Z 0 IdGate

public export
X : {n:Nat} -> (j : Nat) -> {auto prf : LT j n}-> Unitary n -> Unitary n
X {n} j g = ?plusminuslemma $ H (justFinLemma j (minus n j) {prf = lteOneMinus prf}) (Z j (H (justFinLemma j (minus n j) {prf = lteOneMinus prf}) (?plusminuslemmaagain $ g)) {prf = ?sjLTjplusnminusj})

public export
XGate : Unitary 1
XGate = X 0 IdGate

public export
RxGate : Double -> Unitary 1
RxGate p = HGate . PGate p . HGate

public export
RyGate : Double -> Unitary 1
RyGate p = SAdjGate . HGate . PGate (-p) . HGate . SGate

public export
RzGate : Double -> Unitary 1
RzGate p = PGate p 


---------------------CONTROLLED VERSIONS-----------------------
|||Toffoli gate
public export
toffoli : Unitary 3
toffoli = 
  let g1 = CNOT 1 2 (H 2 IdGate)
      g2 = CNOT 0 2 (TAdj 2 g1)
      g3 = CNOT 1 2 (T 2 g2)
      g4 = CNOT 0 2 (TAdj 2 g3)
      g5 = CNOT 0 1 (T 1 (H 2 (T 2 g4)))
  in CNOT 0 1 (T 0 (TAdj 1 g5))

|||Controlled Hadamard gate
public export
controlledH : Unitary 2
controlledH =
  let h1 = (IdGate {n=1}) # (SAdjGate . HGate . TGate . HGate . SGate)
      h2 = (IdGate {n=1}) # (SAdjGate . HGate . TAdjGate . HGate . SGate)
  in h1 . CNOTGate . h2

|||Controlled phase gate
public export
controlledP : Double -> Unitary 2
controlledP p = 
  let p1 = CNOT 0 1 (P (p/2) 1 IdGate)
  in CNOT 0 1 (P (-p/2) 1 p1)

export
twoplusminusone : (n:Nat) ->  {auto prf: LTE 1 n} -> 2 + (minus n 1) = S n
twoplusminusone Z = absurd prf
twoplusminusone (S m) = ?easy2
|||Make the controlled version of a gate
public export
controlled : {n : Nat} -> Unitary n -> {auto prf: LTE 2 (S n)} -> Unitary (S n)
controlled IdGate = IdGate
controlled {n} (H j g) = ?finishlater1
  --let p = lemmaControlledInjective n j 
  --in Unitary.apply {n = S n} {i = justFinLemma 2 (minus n 1) } controlledH (controlled g) [0, ?justrewrite3 $ FS j] {prf = p}
controlled (P p j g) = ?finishlater2
  --let p1 = lemmaControlledInjective n j
  --in ?believeme2 $ apply {n = S n} {i =  FS (FS FZ)} (controlledP p) (controlled g) [0, weaken $ weaken $ weaken $ FS j] {prf = p1}
controlled (CNOT c t {prf3} g1) = ?finishlater3
  --let p = lemmaControlledInjective2 n c t 
  --in ?believeme3 $ apply {i =  FS (FS (FS FZ))} {n = S n} toffoli (controlled g) [0, FS c, FS t] {prf = p}

{-apply : {n : Nat} -> {i : Fin n} -> 
    Unitary (finToNat i) -> Unitary n -> 
    (v : Vect (finToNat i) (Fin n)) -> 
    {auto prf : (allDifferentFin v) = True} -> 
    Unitary n 
  
  public export
data Unitary : Nat -> Type where
  IdGate : Unitary n
  H      : (j : Fin n) -> Unitary n -> Unitary n
  P      : (p : Double) -> (j : Fin n) -> Unitary n -> Unitary n
  CNOT   : (c : Fin n) -> (t : Fin n) -> 
            {auto prf3 : Either (LT (finToNat c) (finToNat t)) (LT (finToNat t) (finToNat c))} -> 
            Unitary n -> Unitar
          -}

------------SOME USEFUL FUNCTIONS FOR CREATING GATES-----------

|||Make n tensor products of the same unitary of size 1
public export
tensorn : (n : Nat) -> Unitary 1 -> Unitary n
tensorn 0 _ = IdGate
tensorn (S k) g = g # (tensorn k g)

|||Controls on the n-1 first qubits, target on the last
public export
multipleQubitControlledNOT : (n : Nat) -> Unitary n
multipleQubitControlledNOT 0 = IdGate
multipleQubitControlledNOT 1 = IdGate
multipleQubitControlledNOT 2 = CNOT 0 1 IdGate
multipleQubitControlledNOT (S (S k)) = controlled (multipleQubitControlledNOT (S k))

||| Tensor product of a Vector of Unitary operators
export
tensorMap : {n : Nat} -> {m : Nat} -> (gates : Vect n (Unitary m)) -> Unitary (n*m)
tensorMap [] = IdGate
tensorMap (gate :: gates) = gate # (tensorMap gates)

||| Tensor product of a Vector of single-qubit Unitary operators
export
tensorMapSimple : {n : Nat} -> (gates : Vect n (Unitary 1)) -> Unitary n
tensorMapSimple g = rewrite sym $ multOneRightNeutral n in tensorMap g

---------------------------------------------------------------
-- count the total number of atomic gates in a unitary circuit
export
gateCount : Unitary n -> Nat
gateCount IdGate = 0
gateCount (H j x) = S (gateCount x)
gateCount (P p j x) = S (gateCount x)
gateCount (CNOT c t x) = S (gateCount x)

--count the number of H gates in a unitary circuit
export
Hcount : Unitary n -> Nat
Hcount IdGate = 0
Hcount (H j x) = S (Hcount x)
Hcount (P p j x) = Hcount x
Hcount (CNOT c t x) = Hcount x

--count the number of P gates in a unitary circuit
export
Pcount : Unitary n -> Nat
Pcount IdGate = 0
Pcount (H j x) = Pcount x
Pcount (P p j x) = S (Pcount x)
Pcount (CNOT c t x) = Pcount x


--count the number of CNOT gates in a unitary circuit
export
CNOTcount : Unitary n -> Nat
CNOTcount IdGate = 0
CNOTcount (H j x) = CNOTcount x
CNOTcount (P p j x) = CNOTcount x
CNOTcount (CNOT c t x) = S (CNOTcount x)

----------------------------DEPTH------------------------------
|||Compute the depth of  circuit

addDepth : Nat -> (j : Fin n) -> Vect n Nat -> Vect n Nat
addDepth j 0 (x :: xs) = j :: xs
addDepth j (FS k) (x :: xs) = x :: addDepth j k xs

{-
addDepth : Nat -> (j : Nat) -> Vect n Nat -> {auto prf : j < n = True} -> Vect n Nat
addDepth j 0 (x :: xs) = j :: xs
addDepth j (S k) (x :: xs) = x :: addDepth j k xs
-}

findValue : (j : Fin n) -> Vect n Nat -> Nat
findValue 0 (x::xs) = x
findValue (FS k) (x::xs) = findValue k xs

{-
findValue : (j : Nat) -> Vect n Nat -> {auto prf : j < n = True} -> Nat
findValue 0 (x::xs) = x
findValue (S k) (x::xs) = findValue k xs
-}
depth' : {n : Nat} -> Unitary n -> Vect n Nat
depth' IdGate = replicate n 0
depth' (H j x) =
  let v = depth' x 
      k = findValue j v
  in addDepth (S k) j v
depth' (P p j x) = 
  let v = depth' x
      k = findValue j v
  in addDepth (S k) j v
depth' (CNOT c t x) = 
  let v = depth' x 
      k = findValue c v
      m = findValue t v
  in if k < m then
              let w = addDepth (S m) c v
              in addDepth (S m) t w
     else
              let w = addDepth (S k) c v
              in addDepth (S k) t w

export
depth : {n : Nat} -> Unitary n -> Nat
depth g = 
  let v = depth' g 
  in foldl max 0 v

----------------------------SHOW-------------------------------
|||For printing the phase gate (used for show, export to Qiskit and draw in the terminal)
|||printPhase : phase -> precision -> string for pi -> String
private
printPhase : Double -> Double -> String -> String
printPhase x epsilon s =
  if x >= pi - epsilon && x <= pi + epsilon then s
  else if x >= pi/2 - epsilon && x <= pi/2 + epsilon then s ++ "/2"
  else if x >= pi/3 - epsilon && x <= pi/3 + epsilon then s ++ "/3"
  else if x >= pi/4 - epsilon && x <= pi/4 + epsilon then s ++ "/4"
  else if x >= pi/6 - epsilon && x <= pi/6 + epsilon then s ++ "/6"
  else if x >= pi/8 - epsilon && x <= pi/8 + epsilon then s ++ "/8"
  else if x >= -pi - epsilon && x <= -pi + epsilon then "-" ++ s
  else if x >= -pi/2 - epsilon && x <= -pi/2 + epsilon then "-" ++ s ++ "/2"
  else if x >= -pi/3 - epsilon && x <= -pi/3 + epsilon then "-" ++ s ++ "/3"
  else if x >= -pi/4 - epsilon && x <= -pi/4 + epsilon then "-" ++ s ++ "/4"
  else if x >= -pi/6 - epsilon && x <= -pi/6 + epsilon then "-" ++ s ++ "/6"
  else if x >= -pi/8 - epsilon && x <= -pi/8 + epsilon then "-" ++ s ++ "/8"
  else show x

public export
Show (Unitary n) where
  show IdGate = ""
  show (H j x) = "(H " ++ show j ++ ") " ++ show x 
  show (P p j x) = "(P " ++ printPhase p 0.001 "π" ++ " " ++ show j ++ ") " ++ show x
  show (CNOT c t x) = "(CNOT " ++ show c ++ " " ++ show t ++ ") " ++ show x



-----------------DRAW CIRCUITS IN THE TERMINAL-----------------

private
newWireQVect : (n : Nat) -> Vect n String
newWireQVect Z = []
newWireQVect (S k) = "" :: newWireQVect k

private
addSymbolProxy : Nat -> Bool -> (String, String) -> Vect n String -> Vect n String
addSymbolProxy _ _ _ [] = []
addSymbolProxy 0 False (s1, s2) (x :: xs) = (x ++ s1) :: addSymbolProxy 0 True  (s1, s2) xs
addSymbolProxy 0 True  (s1, s2) (x :: xs) = (x ++ s2) :: addSymbolProxy 0 True  (s1, s2) xs
addSymbolProxy (S k) _ (s1, s2) (x :: xs) = (x ++ s2) :: addSymbolProxy k False (s1, s2) xs

-- This is necessary due to a technicality (that So is unable to lift a boolean asking for a general comparison between 0 and a len). It's possible to get around this but it unnecessary;
-- since we start with Fin n being smaller than n, we can transition back to a Nat for this operation. It also does not matter, since this is only a local visual aid
private
addSymbol: {n:Nat} -> Fin n -> Bool -> (String, String) -> Vect n String -> Vect n String
addSymbol _ _ _ [] = []
addSymbol k b strs xs = addSymbolProxy (finToNat k) b strs xs

{-}
addSymbol : Nat -> Bool -> (String, String) -> Vect n String -> Vect n String
addSymbol _ _ _ [] = []
addSymbol 0 False (s1, s2) (x :: xs) = (x ++ s1) :: addSymbol 0 True  (s1, s2) xs
addSymbol 0 True  (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol 0 True  (s1, s2) xs
addSymbol (S k) _ (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol k False (s1, s2) xs
-}
 

private
addSymbolCNOT : {n:Nat} -> (Nat, Nat) -> Bool -> Bool -> (v: Vect n String) -> Vect n String
addSymbolCNOT _ _ _ [] = []
addSymbolCNOT (0,0)    False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0,0) True b xs
addSymbolCNOT (0, S k) False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, k) True b xs
addSymbolCNOT (0, 0)   b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (0, 0) b True xs
addSymbolCNOT (S k, 0) b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (k, 0) b True xs
addSymbolCNOT (0, 0) True True (x :: xs) = (x ++ "-----") :: addSymbolCNOT (0, 0) True True xs
addSymbolCNOT (S j, S k) _ _   (x :: xs) = (x ++ "-----") :: addSymbolCNOT (j, k) False False xs
addSymbolCNOT (0, S k) True _  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (0, k) True False xs
addSymbolCNOT (S k, 0) _ True  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (k, 0) False True xs

--this is necessary due to a technicality (that So is unable to lift a boolean asking for a general comparison between 0 and a len). It's possible to get around this but it unnecessary;
-- since we start with Fin n being smaller than n, we can transition back to a Nat for this operation. It also does not matter, since this is only a local visual aid
private
addSymbolCNOTStart : {n:Nat} -> (Fin n, Fin n) -> Bool -> Bool -> (v: Vect n String) -> Vect n String
addSymbolCNOTStart _ _ _ [] = []
addSymbolCNOTStart (k,m) b1 b2 xs = addSymbolCNOT (finToNat k, finToNat m) b1 b2 xs

{-}
addSymbolCNOT : (Nat, Nat) -> Bool -> Bool -> Vect n String -> Vect n String
addSymbolCNOT _ _ _ [] = []
addSymbolCNOT (0,0)    False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, 0) True b xs
addSymbolCNOT (0, S k) False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, k) True b xs
addSymbolCNOT (0, 0)   b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (0, 0) b True xs
addSymbolCNOT (S k, 0) b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (k, 0) b True xs
addSymbolCNOT (0, 0) True True (x :: xs) = (x ++ "-----") :: addSymbolCNOT (0, 0) True True xs
addSymbolCNOT (S j, S k) _ _   (x :: xs) = (x ++ "-----") :: addSymbolCNOT (j, k) False False xs
addSymbolCNOT (0, S k) True _  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (0, k) True False xs
addSymbolCNOT (S k, 0) _ True  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (k, 0) False True xs
-}
private
drawWirePhase : Nat -> String
drawWirePhase 0 = ""
drawWirePhase (S n) = "-" ++ drawWirePhase n

private
drawGate : {n : Nat} -> Unitary n -> Vect n String
drawGate {n} IdGate = newWireQVect n
drawGate (H i g) = addSymbol i False ("- H -", "-----") (drawGate g)
drawGate (P p i g) =
  let epsilon = 0.001 in
  if pi/4 - epsilon <= p && pi/4 + epsilon >= p
    then addSymbol i False ("- T -", "-----") (drawGate g)
  else if -pi/4 - epsilon <= p && -pi/4 + epsilon >= p
    then addSymbol i False ("- T+ -", "------") (drawGate g)
  else if pi/2 - epsilon <= p && pi/2 + epsilon >= p
    then addSymbol i False ("- S -", "-----") (drawGate g)
  else if -pi/2 - epsilon <= p && -pi/2 + epsilon >= p
    then addSymbol i False ("- S+ -", "------") (drawGate g)
  else if pi - epsilon <= p && pi + epsilon >= p
    then addSymbol i False ("- Z -", "-----") (drawGate g)
  else let s = printPhase p epsilon "π"
  in addSymbol i False ("- P(" ++ s ++ ") -", drawWirePhase (length s + 7)) (drawGate g)
drawGate (CNOT i j g) = addSymbolCNOTStart (i,j) False False (drawGate g)


private
drawVect : Vect n String -> String
drawVect [] = ""
drawVect (x :: xs) = x ++ "\n" ++ drawVect xs

|||Draw a circuit in the terminal
public export
draw : {n : Nat} ->  Unitary n -> IO ()
draw g =
  let vs1 = drawGate {n} g in
  let s = drawVect vs1 in
  putStrLn s



--------------------------EXPORT TO QISKIT---------------------

private
unitarytoQiskit : Unitary n -> String
unitarytoQiskit IdGate = ""
unitarytoQiskit (H i g) = unitarytoQiskit g ++  "qc.h(qr[" ++ show i ++ "])\n"
unitarytoQiskit (P p i g) = unitarytoQiskit g ++ "qc.p(" ++ printPhase p 0.001 "np.pi" ++ ", qr[" ++ show i ++ "])\n" 
unitarytoQiskit (CNOT c t g) = unitarytoQiskit g ++ "qc.cx(qr[" ++ show c ++ "], qr[" ++ show t ++ "])\n" 


private
toQiskit : {n : Nat} -> Unitary n -> String
toQiskit g =
  let s = unitarytoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show n ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nqc.draw('mpl')")

|||Export a circuit to Qiskit code
public export
exportToQiskit : {n : Nat} -> String -> Unitary n -> IO ()
exportToQiskit str g =
  let s = toQiskit g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()



{-
finFSapp2 : (n:Nat) -> (k: Fin (S n)) -> (l : Fin (S n)) -> {prf : FS l = k} -> finToNat (FS l) < (S n) = True
finFSapp2 0 any _ _ impossible
finFSapp2 _ FZ any _ impossible 
finFSapp2 (S m) (FS k) FZ {prf} = Refl
finFSapp2 (S m) (FS k) (FS l) {prf} = rewrite (finFSapp (S (S (S m))) (FS (FS l))) in goal 

export 
finLTNat : (n : Nat) -> (k : Fin n) -> (finToNat k < n = True)
finLTNat 0 any = absurd any
finLTNat (S m) FZ = Refl
finLTNat (S m) (FS l) = rewrite (finFSapp (S m) l) in finToNat (FS l) < S m = True
-}


