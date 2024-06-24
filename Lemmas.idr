module Lemmas

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import Complex
import NatRules

%default total

public export
data Qubit : Type where
  MkQubit : (n : Nat) -> Qubit

export
lemmaplusOneRight : (n : Nat) -> n + 1 = S n
lemmaplusOneRight n = rewrite plusCommutative n 1 in Refl

export
%hint
lemmaplusOneRightH : {n : Nat} -> n + 1 = S n
lemmaplusOneRightH {n = n} = rewrite plusCommutative n 1 in Refl

export
%hint
lemmaplusOneRightHSym : {n : Nat} ->  S n = n + 1 
lemmaplusOneRightHSym {n = n} = sym $ rewrite plusCommutative n 1 in Refl

export
lemmaPlusSRight : (n : Nat) -> (k : Nat) -> plus n (S k) = S (plus n k)
lemmaPlusSRight Z     k = Refl
lemmaPlusSRight (S p) k = rewrite lemmaPlusSRight p k in Refl

--restatement of mirror locally 
export
mirror : Either a b -> Either b a
mirror (Left  x) = Right x
mirror (Right x) = Left x

--successives of LT inside Either
eitherLTSucc :{a,b:Nat} -> Either (LT (S a) (S b)) (LT (S b) (S a)) -> Either (LT a b) (LT b a)
eitherLTSucc (Left a) = Left (fromLteSucc a)
eitherLTSucc (Right b) = Right (fromLteSucc b)

eitherLTtoSucc : Either (LT a b) (LT b a) -> Either (LT (S a) (S b)) (LT (S b) (S a))
eitherLTtoSucc (Left a) = Left (LTESucc a)
eitherLTtoSucc (Right b) = Right (LTESucc b)

--LEMMAS ABOUT &&

export
lemmaAndLeft : {a : Bool} -> {b : Bool} -> (a && b = True) -> (a = True)
lemmaAndLeft {a = True} {b} p =  Refl
lemmaAndLeft {a = False} {b} p impossible

export
lemmaAndRight : {a : Bool} -> {b : Bool} -> (a && b = True) -> (b = True)
lemmaAndRight {a} {b = True} p = Refl
lemmaAndRight {a = True} {b = False} p impossible
lemmaAndRight {a = False} {b = False} p impossible

export
lemmaAnd : {a : Bool} -> {b : Bool} -> (a = True) -> (b = True) -> (a && b = True)
lemmaAnd {a = True} {b = True} p1 p2 = Refl



--BASIC LEMMAS ABOUT <, >, =, /=, <=, >=

export
||| `LTE` is reflexive.
lteRefl : (n:Nat) -> LTE n n
lteRefl Z   = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

export
%hint
lteReflHint : {n:Nat} -> LTE n n
lteReflHint {n} = lteRefl n 

export
lemmaLTERefl : (n : Nat) -> LTE n n
lemmaLTERefl any = lteRefl any

export
lemmaSymDiff : {x : Nat} -> {y : Nat} -> (x /= y) = True -> (y /= x) = True
lemmaSymDiff {x = 0} {y = (S m)} _ = Refl
lemmaSymDiff {x = (S k)} {y = 0} _ = Refl
lemmaSymDiff {x = (S k)} {y = (S j)} prf = lemmaSymDiff {x = k} {y = j} prf


export 
%hint
lemma1LTESucc : (k : Nat) -> LTE 1 (S k)
lemma1LTESucc 0 = lteRefl 1
lemma1LTESucc (S k) = lteSuccRight $ lemma1LTESucc k

export 
%hint
lemma0LTSucc : (k : Nat) -> LT 0 (S k)
lemma0LTSucc Z = lteRefl 1
lemma0LTSucc (S k) = lteSuccRight $ lemma0LTSucc k


export 
%hint
lemmaLTEAddR : (n : Nat) -> (p : Nat) -> LTE n (n+p)
lemmaLTEAddR Z 0 = lteRefl Z
lemmaLTEAddR Z (S k) = LTEZero
lemmaLTEAddR (S n) p = LTESucc $ lemmaLTEAddR n p

export 
%hint
lemmaLTEAddL : (n : Nat) -> (p : Nat) -> LTE p (n+p)
lemmaLTEAddL n p = rewrite plusCommutative n p in lemmaLTEAddR p n


export 
%hint
lemmaDiffSuccPlus : (k : Nat) -> (p : Nat) -> (k /= S (p + k)) = True
lemmaDiffSuccPlus 0 p = Refl
lemmaDiffSuccPlus (S k) j = rewrite sym $ plusSuccRightSucc j k in lemmaDiffSuccPlus k j

export 
%hint
lemmaLTSuccPlus : (k : Nat) -> (p : Nat) -> LT k (S (k+p))
lemmaLTSuccPlus 0 0 = lteRefl 1
lemmaLTSuccPlus 0 (S j) = lteSuccRight $ fromLteSucc $ LTESucc $ lemmaLTSuccPlus 0 j
lemmaLTSuccPlus (S k) j = LTESucc $ lemmaLTSuccPlus k j

export 
%hint
lemmaLTSucc : (k : Nat) -> LT k (S k)
lemmaLTSucc 0 = lteRefl 1
lemmaLTSucc (S k) = LTESucc $ lemmaLTSucc k

export 
%hint
lemmakLTSk : (k : Nat) -> LT (S k) (S (k+1))
lemmakLTSk k = rewrite lemmaplusOneRight k in (LTESucc $ lemmaLTSucc k)

export 
%hint
lemmaLTSuccLT : (k : Nat) -> (n : Nat) -> LT (S k) n -> LT k n
lemmaLTSuccLT k 0 prf impossible
lemmaLTSuccLT 0 n prf = fromLteSucc $ lteSuccRight prf
lemmaLTSuccLT (S k) (S n) prf = lteSuccLeft prf

export 
%hint
lemmaLTESuccLT : (k : Nat) -> (n : Nat) -> LTE (S k) n -> LT k n
lemmaLTESuccLT k 0 prf impossible
lemmaLTESuccLT 0 n prf = prf
lemmaLTESuccLT (S k) (S j) prf = prf


export 
%hint
lemmaLTESuccLTE : (k : Nat) -> (n : Nat) -> LTE (S k) n -> LTE k n
lemmaLTESuccLTE k 0 prf impossible
lemmaLTESuccLTE 0 _ _ = LTEZero
lemmaLTESuccLTE (S k) (S j) prf = lteSuccLeft prf

export 
%hint
lemmaSuccsLT : (k : Nat) -> (n : Nat) -> LT (S k) (S n) -> LT k n
lemmaSuccsLT k n prf = fromLteSucc prf

export 
%hint
lemmaCompLT0 : (n : Nat) -> (j : Nat) -> {auto prf : LT j n} -> LT 0 n
lemmaCompLT0 n 0 {prf} = prf
lemmaCompLT0 p (S k) {prf} = lemmaCompLT0 p k {prf = fromLteSucc $ lteSuccRight prf}

export 
%hint
sPlusEq : {k:Nat} -> {m:Nat} -> S (plus k m) = plus k (S m)
sPlusEq {k=k} {m=m} = rewrite plusSuccRightSucc k m in Refl

--LEMMAS ABOUT <, >, =, /=, <=, >= : TRANSITIVITY

export 
%hint
lemmaTransLTESLTE : (i : Nat) -> (n : Nat) -> (p : Nat) -> LTE i n -> LTE (S n) p -> LTE (S i) p
lemmaTransLTESLTE 0 0 (S k) _ _ = lemma1LTESucc k
lemmaTransLTESLTE i n k prf1 prf2 = lteTransitive (LTESucc prf1) prf2
--lemmaTransLTESLTE (S k) (S n) (S p) prf1 prf2 =  lteTransitive (LTESucc prf1) prf2 --LTESucc $ lemmaTransLTESLTE k n p (fromLteSucc prf1) (fromLteSucc prf2)

export
lemmaTransLTELT : (i : Nat) -> (n : Nat) -> (p : Nat) -> LTE i n -> LT n p -> LT i p
lemmaTransLTELT = lemmaTransLTESLTE

export
lemmaTransLTLTE : (i : Nat) -> (n : Nat) -> (p : Nat) -> LT i n -> LTE n p -> LT i p
lemmaTransLTLTE i n k prf1 prf2 = lteTransitive prf1 prf2

export
lemmaTransitivity : (i : Nat) -> (n : Nat) -> (p : Nat) -> LT i n -> LT n p -> LT i p
lemmaTransitivity i n k prf1 prf2 = lteTransitive prf1 (lteSuccLeft prf2)


--LEMMAS USED BY THE APPLY FUNCTION
export
indexInjectiveVect : (j : Nat) -> (n : Nat) -> (v : Vect i Nat) ->
                     {auto prf : IsInjectiveT n v} -> {prf1 : LT j i} ->
                     LT (indexLT j v) n
indexInjectiveVect Z n (x :: xs) {prf} = getPrfSmaller $ getAllSmaller prf
indexInjectiveVect (S k) n (x :: xs) {prf} = indexInjectiveVect k n xs {prf = ifInjectiveThenSubInjective prf}
 

export
different' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : LT m i} -> {prf2 : IsDifferentT x xs} ->
             Either (LT x (indexLT m xs)) (LT (indexLT m xs) x)
different' x 0 (y :: xs) = isDiffToPrf prf2
different' x (S k) (y :: xs) = different' x k xs {prf1 = fromLteSucc prf1} {prf2 = ifDiffThenSubDiff prf2}

private
different'' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : LT m i} -> {prf2 : IsDifferentT x xs} ->
              Either (LT (indexLT m xs) x) (LT x (indexLT m xs)) 
different'' x 0 (y :: xs) =  mirror $ isDiffToPrf prf2
different'' x (S k) (y :: xs) = different'' x k xs {prf1 = fromLteSucc prf1} {prf2 = ifDiffThenSubDiff prf2}
             

export
differentIndexInjectiveVect : (c : Nat) -> (t : Nat) -> (n : Nat) -> {prf1 :  Either (LT c t) (LT t c)} ->
                              (v : Vect i Nat) -> {prf2 : IsInjectiveT n v} ->
                              {prf3 : LT c i } -> {prf4 : LT t i } ->
                              Either (LT (indexLT c v) (indexLT t v)) (LT (indexLT t v) (indexLT c v))
differentIndexInjectiveVect 0 0 _ _ = absurd prf1
differentIndexInjectiveVect 0 (S m) n (x :: xs) =
      different' x m xs {prf1 = fromLteSucc prf4} {prf2 = allDiffToPrf $ getAllDifferent prf2}
differentIndexInjectiveVect (S k) 0 n (x :: xs) =
      different'' x k xs {prf1 = fromLteSucc prf3} {prf2 = allDiffToPrf $ getAllDifferent prf2}
differentIndexInjectiveVect (S k) (S j) n (x :: xs) =
  differentIndexInjectiveVect k j n {prf1 = eitherLTSucc prf1} xs {prf2 = ifInjectiveThenSubInjective prf2} {prf3 = fromLteSucc prf3} {prf4 = fromLteSucc prf4}

--------------------------------------------------------------------
--------------LEMMAS USED BY THE CONTROLLED FUNCTION ---------------
--------------------------------------------------------------------

--Small helper lemmas to make the actual functions look less messy--
ltz1: LT 0 1
ltz1 = lteRefl 1

ltzs: (k:Nat) -> LT Z (S k) 
ltzs 0 = lteRefl 1  
ltzs (S k) = lteSuccRight $ ltzs k

ltzss: (k:Nat) -> LT Z (S (S k)) 
ltzss 0 = LTESucc LTEZero 
ltzss (S k) = lteSuccRight $ ltzss k

lt1ss: (k:Nat) -> LT 1 (S (S k))
lt1ss Z = lteRefl 2
lt1ss (S k) = lteSuccRight $ lt1ss k

--------------------------------------------------------------------

export
lemmaControlledInj : (n : Nat) -> (j : Nat) -> {auto prf : LT j n} -> IsInjectiveT (S n) [0, S j]
lemmaControlledInj 0 0 impossible
lemmaControlledInj 0 (S k) {prf} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss k)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
  (ASSucc (ltz1) (ASSucc (LTESucc prf) (ASNil)))
lemmaControlledInj (S k) 0 = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltz1)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf) (ASNil)))
lemmaControlledInj (S p) (S k) {prf} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss k)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
  (ASSucc (ltzss p) (ASSucc (LTESucc prf) (ASNil)))

export
lemmaControlledInj2 : (n : Nat) -> (c : Nat) -> (t : Nat) ->
                      {auto prf1 : LT c n} -> {auto prf2 : LT t n} -> {auto prf3 : Either (LT c t) (LT t c)} ->
                      IsInjectiveT (S n) [0, S c, S t]
lemmaControlledInj2 0 0 t impossible
lemmaControlledInj2 0 (S k) t {prf1} {prf2} {prf3}= IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss k)) (IsDiffSucc (Left (ltzs t)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (eitherLTtoSucc prf3) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltz1) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) 0 0 {prf3} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltz1)) (IsDiffSucc (Left (ltz1)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (eitherLTtoSucc prf3) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) 0 (S j) = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltz1)) (IsDiffSucc (Left (ltzss j)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (Left (lt1ss j)) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) (S j) 0 = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss j)) (IsDiffSucc (Left (ltz1)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (Right (lt1ss j)) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) (S j) (S i) = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss j)) (IsDiffSucc (Left (ltzss i)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (eitherLTtoSucc prf3) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))
                      
export 
%hint
lemmaIsDiffGen : (m:Nat) -> (v: Vect n Nat) -> IsDifferentT m v
lemmaIsDiffGen m [] = IsDiffNil
lemmaIsDiffGen m (x::xs) = case isLT m x of
   Yes prfLeft => IsDiffSucc (Left prfLeft) (lemmaIsDiffGen m xs)
   No prfNo1 => case isLT x m of
    Yes prfRight =>  IsDiffSucc (Right prfRight) (lemmaIsDiffGen m xs)
    No prfNo2 => assert_total $ idris_crash "There exists no automatic proof that the Vector is Injective"

export 
%hint    
lemmaAllDiffGen : {v: Vect n Nat} -> AllDifferentT v
lemmaAllDiffGen {v = []} = AllDiffNil
lemmaAllDiffGen {v = (x::xs)} = AllDiffSucc (lemmaIsDiffGen x xs) (lemmaAllDiffGen {v = xs})

export 
%hint 
lemmaAllSmallGen : (m:Nat) -> (v: Vect n Nat) -> AllSmallerT v m
lemmaAllSmallGen {m} {v = []} = ASNil
lemmaAllSmallGen {m} {v = (x::xs)} = case isLT x m of
  Yes prfLT => ASSucc prfLT (lemmaAllSmallGen {m = m} {v = xs})
  No prfNo1 =>assert_total $ idris_crash "There exists no automatic proof that the Vector is Injective"

export 
%hint 
lemmaIsInjectiveT : {m:Nat} -> {v: Vect n Nat} -> IsInjectiveT m v
lemmaIsInjectiveT {m} {v} = IsInjectiveSucc (lemmaAllDiffGen {v = v}) (lemmaAllSmallGen {m = m} {v = v})

export 
%hint 
lemmaIsInjectiveTk : {m: Nat -> Nat} -> {v: Nat-> Vect n Nat} -> ({k: Nat} -> IsInjectiveT (m k) (v k))
lemmaIsInjectiveTk {m} {v} = IsInjectiveSucc (lemmaAllDiffGen {v = v k}) (lemmaAllSmallGen {m = m k} {v = v k})

{-
export
%hint
lemmaSuccInjg: {k:Nat} -> IsInjectiveT (S (S k)) [S k, 0]
lemmaSuccInjg {k} = lemmaIsInjectiveTk {m = \l => S (S k)} {v = \d => [ S d, 0]}

export
%hint
lemmaSuccInj: {k:Nat} -> IsInjectiveT (S (S k)) [S k, 0]
lemmaSuccInj {k} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Right (ltzs k)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
(ASSucc (lteRefl (S (S k))) (ASSucc (ltzss k) (ASNil))) 


export
%hint
lemmaSuccInjPlus: {k:Nat} -> IsInjectiveT (S (k + 1)) [S k, 0]  
lemmaSuccInjPlus {k} = rewrite sym $ Data.Nat.plusOneSucc k in (rewrite plusCommutative k 1 in lemmaSuccInjg)-}

--LEMMAS USED BY THE TENSOR FUNCTION
export
lemmaDiffSuccPlusE : (k : Nat) -> (p : Nat) -> Either (LT k (S (p + k))) (LT (S (p + k)) k)
lemmaDiffSuccPlusE 0 p = rewrite plusZeroRightNeutral p in Left (ltzs p)
lemmaDiffSuccPlusE (S k) j = (rewrite sym $ plusSuccRightSucc j k in (eitherLTtoSucc (lemmaDiffSuccPlusE k j)))

export
isDiffRangeVect : (k : Nat) -> (length : Nat) -> (p : Nat) -> IsDifferentT k (rangeVect (S (p + k)) length)
isDiffRangeVect k 0 _ = IsDiffNil
isDiffRangeVect k (S j) p = IsDiffSucc (lemmaDiffSuccPlusE k p) (isDiffRangeVect k j (S p))

export
allDiffRangeVect : (startIndex : Nat) -> (length : Nat) -> AllDifferentT (rangeVect startIndex length)
allDiffRangeVect startIndex 0 = AllDiffNil
allDiffRangeVect startIndex (S k) = 
  let p1 = isDiffRangeVect startIndex k 0
  in AllDiffSucc p1 (allDiffRangeVect (S startIndex) k)

export
allSmallerRangeVect : (startIndex : Nat) -> (length : Nat) -> AllSmallerT (rangeVect startIndex length) (startIndex + length)
allSmallerRangeVect startIndex 0 = ASNil
allSmallerRangeVect startIndex (S k) = 
  rewrite sym $ plusSuccRightSucc startIndex k in 
          ASSucc (lemmaLTSuccPlus startIndex k) (allSmallerRangeVect (S startIndex) k) 

export
allSmallerPlus : (n : Nat) -> (p : Nat) -> (v : Vect k Nat) -> AllSmallerT v n -> AllSmallerT v (n + p)
allSmallerPlus n p [] prf = ASNil
allSmallerPlus n p v prf = ifAllSmallThenPlusSmall p prf 

export 
isInjectiveRangeVect : (startIndex : Nat) -> (length : Nat) -> IsInjectiveT (startIndex+length) (rangeVect startIndex length)
isInjectiveRangeVect i length = IsInjectiveSucc (allDiffRangeVect i length) (allSmallerRangeVect i length)
