module Injection

import Data.Vect
import Data.Nat
import Neq
import LinearTypes
import Decidable.Equality

%default total
-----------------------Syntactic tests for either----------------------------

||| True if the argument is Left, False otherwise
export
isLeft : Either a b -> Bool
isLeft (Left l)  = True
isLeft (Right r) = False
    
||| True if the argument is Right, False otherwise
export
isRight : Either a b -> Bool
isRight (Left l)  = False
isRight (Right r) = True

----LTE transitivity restated from library ----------------------------------
export 
||| `LTE` is transitive frommain library, unimported
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)
-----------------------------------------------------------------------------

|||Is a Nat different from all the Nats in a vector?
public export
isDifferent : Nat -> Vect n Nat -> Bool
isDifferent n [] = True
isDifferent n (x :: xs) = (n /= x) && isDifferent n xs

|||Are all the elements of a Nat vector different?
public export
allDifferent : Vect n Nat -> Bool
allDifferent [] = True
allDifferent (x :: xs) = isDifferent x xs && allDifferent xs

|||Are all the elements in a vector smaller than a given Nat?
public export 
allSmaller : Vect n Nat -> Nat -> Bool
allSmaller [] m = True
allSmaller (x :: xs) m = (x < m) && allSmaller xs m


public export
isInjective : Nat -> Vect n Nat -> Bool
isInjective m v = allSmaller v m && allDifferent v


|||Returns the element at index k in a vector
public export
index : (k : Nat) -> Vect n Nat -> {auto prf : (k < n) = True} -> Nat
index Z     (x::_)  = x
index (S k) (_::xs) = index k xs

public export
indexLT : (k : Nat) -> Vect n Nat -> {auto prf : LT k n} -> Nat
indexLT Z     (x::_) {prf} = x
indexLT (S k) (_::xs) {prf} = indexLT k xs {prf = fromLteSucc prf}

public export
indexLTL : (k : Nat) -> (1_: Vect n Nat) -> {auto prf : LT k n} -> LFstPair (Vect n Nat) Nat
indexLTL Z (x::xs) {prf} = (x::xs) # x
indexLTL (S k) (x::xs) {prf} = let (qs # m) = indexLTL k xs {prf = fromLteSucc prf} in (x :: qs) # m

|||Returns the vector [1,2,...,n]
public export
rangeVect : (startIndex : Nat) -> (length : Nat) -> Vect length Nat
rangeVect k Z = []
rangeVect k (S i) = k :: rangeVect (S k) i

------------------------------------------------------------------------------
---------------------------------------------------------------------------
public export
data AllSmallerT : (v: Vect n Nat) -> (m:Nat) -> Type where
    ASNil  : AllSmallerT [] m 
    ASSucc :  LT x m -> (soFarSmaller: AllSmallerT xs m)-> AllSmallerT (x :: xs) m

export
getPrfSmaller : AllSmallerT v m -> LT (head v) m
getPrfSmaller ASNil impossible
getPrfSmaller (ASSucc prf sfs) = prf

|||Are all the elements in a vector smaller than a given Nat?
public export 
allSmallerT : Vect n Nat -> Nat -> Type
allSmallerT v m = AllSmallerT v m 

export
ifAllSmallThenSubSmall : AllSmallerT (x::xs) m -> AllSmallerT xs m
ifAllSmallThenSubSmall (ASSucc a b) = b

export
plusLT : {a,b:Nat} -> (c:Nat) -> LT a b -> LT a (b+c)
plusLT Z prf = rewrite plusZeroRightNeutral b in prf 
plusLT {a} {b} (S c) prf = lteTransitive prf (lteAddRight b)

export
ifAllSmallThenPlusSmall : {v: Vect k Nat} -> {m: Nat} -> (n:Nat) -> AllSmallerT v m -> AllSmallerT v (m+n) 
ifAllSmallThenPlusSmall any ASNil = ASNil
ifAllSmallThenPlusSmall Z prf = rewrite plusZeroRightNeutral m in prf 
ifAllSmallThenPlusSmall {v = (x::xs)} {m} (S n) (ASSucc (lt) prev) =  ASSucc (plusLT {a = x} {b = m} (S n) lt) (ifAllSmallThenPlusSmall (S n) prev)

public export
data IsDifferentT : (m: Nat) -> (v: Vect n Nat) -> Type where
    IsDiffNil  : IsDifferentT m []
    IsDiffSucc : (Either (LT m x) (LT x m)) -> (soFarDiff: IsDifferentT m xs)-> IsDifferentT m (x :: xs)

export
isDifferentT : Nat -> Vect n Nat -> Type
isDifferentT n v = IsDifferentT n v

export
ifDiffThenSubDiff : IsDifferentT m (x::xs) -> IsDifferentT m xs
ifDiffThenSubDiff (IsDiffSucc a b) = b

export
isDiffToPrf : IsDifferentT m (x::xs) -> Either (LT m x) (LT x m)
isDiffToPrf (IsDiffSucc a b) = a

public export
data AllDifferentT : (v: Vect n Nat) -> Type where
    AllDiffNil  : AllDifferentT []
    AllDiffSucc : IsDifferentT x xs -> (soFarDiff: AllDifferentT xs)-> AllDifferentT (x :: xs)

export
ifAllDiffThenSubDiff : AllDifferentT (x::xs) -> AllDifferentT xs
ifAllDiffThenSubDiff (AllDiffSucc a b) = b

export
allDiffToPrf: AllDifferentT (x::xs) -> IsDifferentT x xs
allDiffToPrf (AllDiffSucc a b) = a

public export
allDifferentT : Vect n Nat -> Type
allDifferentT v = AllDifferentT v

public export
data IsInjectiveT : (m:Nat) -> (v: Vect n Nat) -> Type where
    IsInjectiveSucc : AllDifferentT v -> AllSmallerT v m-> IsInjectiveT m v

public export
isInjectiveT : Nat -> Vect n Nat -> Type
isInjectiveT m v = IsInjectiveT m v

export
getAllSmaller: IsInjectiveT m v -> AllSmallerT v m
getAllSmaller (IsInjectiveSucc prf1 prf2) = prf2

export
getAllDifferent : IsInjectiveT m v -> AllDifferentT v
getAllDifferent (IsInjectiveSucc prf1 prf2) = prf1

export
ifInjectiveThenSubInjective : IsInjectiveT m (x::xs) -> IsInjectiveT m xs
ifInjectiveThenSubInjective (IsInjectiveSucc allDiff allSmall)= IsInjectiveSucc (ifAllDiffThenSubDiff allDiff) (ifAllSmallThenSubSmall allSmall)

||| Alternative - equality to Void

public export
data IsDifferentDec : (m: Nat) -> (v: Vect n Nat) -> Type where
    IsDiffNilDec  : IsDifferentDec m []
    IsDiffSuccDec : (m = x -> Void)-> (soFarDiff: IsDifferentDec m xs)-> IsDifferentDec m (x :: xs)

export
isDifferentDec : Nat -> Vect n Nat -> Type
isDifferentDec n v = IsDifferentDec n v

export
ifDiffThenSubDiffDec  : IsDifferentDec  m (x::xs) -> IsDifferentDec m xs
ifDiffThenSubDiffDec (IsDiffSuccDec a b) = b

export
isDiffToPrfDec : IsDifferentDec k (x::xs) -> (k = x -> Void)
isDiffToPrfDec (IsDiffSuccDec a b) = a

export
eqSymVoid : (k = x -> Void) -> (x = k -> Void)
eqSymVoid kxToVoid Refl = kxToVoid Refl


public export
data AllDifferentDec : (v: Vect n Nat) -> Type where
    AllDiffNilDec  : AllDifferentDec []
    AllDiffSuccDec : IsDifferentDec x xs -> (soFarDiff: AllDifferentDec xs)-> AllDifferentDec (x :: xs)

export
ifAllDiffDecThenSubDiffDec : AllDifferentDec (x::xs) -> AllDifferentDec xs
ifAllDiffDecThenSubDiffDec (AllDiffSuccDec a b) = b

export
allDiffDecToPrf : AllDifferentDec (x::xs) -> IsDifferentDec x xs
allDiffDecToPrf (AllDiffSuccDec a b) = a

public export
allDifferentDec : Vect n Nat -> Type
allDifferentDec v = AllDifferentDec v

public export
data IsInjectiveDec : (m:Nat) -> (v: Vect n Nat) -> Type where
    IsInjectiveSuccDec : AllDifferentDec v -> AllSmallerT v m -> IsInjectiveDec m v

public export
isInjectiveDec : Nat -> Vect n Nat -> Type
isInjectiveDec m v = IsInjectiveDec m v

export
getAllSmallerDec : IsInjectiveDec m v -> AllSmallerT v m
getAllSmallerDec (IsInjectiveSuccDec prf1 prf2) = prf2

export
getAllDifferentDec : IsInjectiveDec m v -> AllDifferentDec v
getAllDifferentDec (IsInjectiveSuccDec prf1 prf2) = prf1

export
ifInjectiveDecThenSubInjectiveDec : IsInjectiveDec m (x::xs) -> IsInjectiveDec m xs
ifInjectiveDecThenSubInjectiveDec (IsInjectiveSuccDec allDiff allSmall) =
    IsInjectiveSuccDec (ifAllDiffDecThenSubDiffDec allDiff) (ifAllSmallThenSubSmall allSmall)   

{-public export
data EitherAnd : (sumType: Either a b) -> Type where
    EitherNil : EitherAnd sumType
    EitherCons : (e : sumType) -> (es: EitherAnd (Left e)) -> EitherAnd sum
-}