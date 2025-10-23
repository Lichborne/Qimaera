module InjectionQubits

import Data.Vect
import Data.Nat
import Neq
import LinearTypes
import Decidable.Equality
import Qubit

%default total

------------------------------------------------------------------------------
---------------------------------------------------------------------------
public export
data AllSmallerT : (v: LVect n Qubit) -> (m:Qubit) -> Type where
    ASNil  : AllSmallerT [] m 
    ASSucc :  LTq x m -> (soFarSmaller: AllSmallerT xs m)-> AllSmallerT (x :: xs) m
{-}
export
getPrfSmaller : AllSmallerT v m -> LTq (head v) m
getPrfSmaller ASNil impossible
getPrfSmaller (ASSucc prf sfs) = prf
-}
|||Are all the elements in a vector smaller than a given Qubit?
public export 
allSmallerT : LVect n Qubit -> Qubit -> Type
allSmallerT v m = AllSmallerT v m 

export
ifAllSmallThenSubSmall : AllSmallerT (x::xs) m -> AllSmallerT xs m
ifAllSmallThenSubSmall (ASSucc a b) = b
{-}
export
plusLTq : {a,b:Qubit} -> (c:Qubit) -> LTq a b -> LTq a (b+c)
plusLTq q prf = rewrite plusZeroRightNeutral b in prf 
plusLTq {a} {b} c prf = lteTransitive prf (lteAddRight b)

export
ifAllSmallThenPlusSmall : {v: Vect k Qubit} -> {m: Qubit} -> (n:Qubit) -> AllSmallerT v m -> AllSmallerT v (m+n) 
ifAllSmallThenPlusSmall any ASNil = ASNil
ifAllSmallThenPlusSmall Z prf = rewrite plusZeroRightNeutral m in prf 
ifAllSmallThenPlusSmall {v = (x::xs)} {m} (S n) (ASSucc (lt) prev) =  ASSucc (plusLTq {a = x} {b = m} (S n) lt) (ifAllSmallThenPlusSmall (S n) prev)
-}
public export
data IsDifferentT : (m: Qubit) -> (v: LVect n Qubit) -> Type where
    IsDiffNil  : IsDifferentT m []
    IsDiffSucc : (Either (LTq m x) (LTq x m)) -> (soFarDiff: IsDifferentT m xs) -> IsDifferentT m (x :: xs)

export
isDifferentT : Qubit -> LVect n Qubit -> Type
isDifferentT n v = IsDifferentT n v

export
ifDiffThenSubDiff : IsDifferentT m (x::xs) -> IsDifferentT m xs
ifDiffThenSubDiff (IsDiffSucc a b) = b

export
isDiffToPrf : IsDifferentT m (x::xs) -> Either (LTq m x) (LTq x m)
isDiffToPrf (IsDiffSucc a b) = a

public export
data AllDifferentT : (v: LVect n Qubit) -> Type where
    AllDiffNil  : AllDifferentT []
    AllDiffSucc : IsDifferentT x xs -> (soFarDiff: AllDifferentT xs)-> AllDifferentT (x :: xs)

export
ifAllDiffThenSubDiff : AllDifferentT (x::xs) -> AllDifferentT xs
ifAllDiffThenSubDiff (AllDiffSucc a b) = b

export
allDiffToPrf: AllDifferentT (x::xs) -> IsDifferentT x xs
allDiffToPrf (AllDiffSucc a b) = a

public export
allDifferentT : LVect n Qubit -> Type
allDifferentT v = AllDifferentT v

public export
data IsInjectiveT : (m:Qubit) -> (v: LVect n Qubit) -> Type where
    IsInjectiveSucc : AllDifferentT v -> AllSmallerT v m-> IsInjectiveT m v

public export
isInjectiveT : Qubit -> LVect n Qubit -> Type
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
data IsDifferentDec : (m: Qubit) -> (v: LVect n Qubit) -> Type where
    IsDiffNilDec  : IsDifferentDec m []
    IsDiffSuccDec : (m = x -> Void)-> (soFarDiff: IsDifferentDec m xs)-> IsDifferentDec m (x :: xs)

export
isDifferentDec : Qubit -> LVect n Qubit -> Type
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
data AllDifferentDec : (v: LVect n Qubit) -> Type where
    AllDiffNilDec  : AllDifferentDec []
    AllDiffSuccDec : IsDifferentDec x xs -> (soFarDiff: AllDifferentDec xs)-> AllDifferentDec (x :: xs)

export
ifAllDiffDecThenSubDiffDec : AllDifferentDec (x::xs) -> AllDifferentDec xs
ifAllDiffDecThenSubDiffDec (AllDiffSuccDec a b) = b

export
allDiffDecToPrf : AllDifferentDec (x::xs) -> IsDifferentDec x xs
allDiffDecToPrf (AllDiffSuccDec a b) = a

public export
allDifferentDec : LVect n Qubit -> Type
allDifferentDec v = AllDifferentDec v

public export
data IsInjectiveDec : (m:Qubit) -> (v: LVect n Qubit) -> Type where
    IsInjectiveSuccDec : AllDifferentDec v -> AllSmallerT v m -> IsInjectiveDec m v

public export
isInjectiveDec : Qubit -> LVect n Qubit -> Type
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


export 
findProofIsDiffOrNothing : (m:Qubit) -> (v: LVect n Qubit) -> Maybe (IsDifferentT m v)
findProofIsDiffOrNothing m [] = Just IsDiffNil
findProofIsDiffOrNothing m (x::xs) = case isLTq m x of
   Yes prfLeft => case (findProofIsDiffOrNothing m xs) of 
    Just isdif => Just $ IsDiffSucc (Left prfLeft) isdif
    Nothing => Nothing
   No prfNo1 => case isLTq x m of
     Yes prfRight => case (findProofIsDiffOrNothing m xs) of 
        Just isdif => Just $ IsDiffSucc (Right prfRight) isdif
        Nothing => Nothing
     No prfNo2 => Nothing
     _ => Nothing
   _ => Nothing

isDifSProp : (IsDifferentT m xs -> Void) -> (IsDifferentT m (x :: xs)) -> Void
isDifSProp IsDiffNil void IsDiffNil impossible
isDifSProp (IsDiffSucc either prev) void IsDiffNil impossible
isDifSProp (IsDiffSucc either prev) v (IsDiffSucc eitherx IsDiffNil) impossible
isDifSProp f (IsDiffSucc eitherx prevx) = f prevx

eitherVoid: (left -> Void) -> (right-> Void) -> Either left right -> Void
eitherVoid fleft fright (Left l) = fleft l
eitherVoid fleft fright (Right r) = fright r

eitherVoidThenNotDif : (Either (LTEq (MkQubit (S m)) (MkQubit (x))) (LTEq (MkQubit (S x)) (MkQubit (m))) -> Void) -> IsDifferentT m (x :: xs) -> Void
eitherVoidThenNotDif feither IsDiffNil impossible
eitherVoidThenNotDif feither (IsDiffSucc either prev) = feither either


export 
eitherIsDiffOrNot : (m:Qubit) -> (v: LVect n Qubit) -> Either (IsDifferentT m v) (IsDifferentT m v -> Void)
eitherIsDiffOrNot m [] = Left IsDiffNil
eitherIsDiffOrNot m (x::xs) = 
    case isLTq m x of
        Yes prfLeft => case (eitherIsDiffOrNot m xs) of 
            Left isdif => Left $ IsDiffSucc (Left prfLeft) isdif
            Right notdif => Right (isDifSProp (notdif))
        No prfNo1 => case isLTq x m of
            Yes prfRight => case (eitherIsDiffOrNot m xs) of 
                Left isdif => Left $ IsDiffSucc (Right prfRight) isdif
                Right notdif => Right (isDifSProp (notdif))
            No prfNo2 => Right (eitherVoidThenNotDif $ eitherVoid prfNo1 prfNo2)
  

export 
findProofAllDiffOrNothing : {v: LVect n Qubit} -> Maybe (AllDifferentT v)
findProofAllDiffOrNothing {v = []} = Just AllDiffNil
findProofAllDiffOrNothing {v = (x::xs)} = case (findProofIsDiffOrNothing x xs) of 
    Just isdif => case (findProofAllDiffOrNothing {v = xs}) of 
        Just alldif => Just $ AllDiffSucc isdif alldif
        Nothing => Nothing
    Nothing => Nothing

allDifSProp : (AllDifferentT xs -> Void) -> (AllDifferentT (x :: xs)) -> Void
allDifSProp AllDiffNil void AllDiffNil impossible
allDifSProp (AllDiffSucc either prev) void AllDiffNil impossible
allDifSProp (AllDiffSucc either prev) v (AllDiffSucc eitherx AllDiffNil) impossible
allDifSProp f (AllDiffSucc eitherx prevx) = f prevx

notAllDiffProp : (IsDifferentT x xs -> Void) -> AllDifferentT (x :: xs) -> Void
notAllDiffProp tovoid AllDiffNil impossible
notAllDiffProp tovoid (AllDiffSucc isdif prev) = tovoid isdif


export 
%hint
eitherAllDiffOrNot  : {v: LVect n Qubit} -> Either (AllDifferentT v) (AllDifferentT v -> Void)
eitherAllDiffOrNot  {v = []} = Left AllDiffNil
eitherAllDiffOrNot {v = (x::xs)} = case (eitherIsDiffOrNot x xs) of 
    Left isdif => case (eitherAllDiffOrNot {v = xs}) of 
        Left alldif => Left (AllDiffSucc isdif alldif)
        Right notalldif => Right (allDifSProp notalldif)
    Right notalldif => Right (notAllDiffProp (notalldif))


export 
findProofAllSmallerOrNothing : (m:Qubit) -> (v: LVect n Qubit) -> Maybe (AllSmallerT v m)
findProofAllSmallerOrNothing {m} {v = []} = Just ASNil
findProofAllSmallerOrNothing {m} {v = (x::xs)} = case isLTq x m of
  Yes prfLTq => case (findProofAllSmallerOrNothing {m = m} {v = xs}) of 
    Just allsmaller => Just $ ASSucc prfLTq allsmaller
    Nothing => Nothing
  No prfNo1 => Nothing

allSmallSProp : (AllSmallerT xs m -> Void) -> AllSmallerT (x :: xs) m -> Void
allSmallSProp ASNil void ASNil impossible
allSmallSProp (ASSucc lt prev) void ASNil impossible
allSmallSProp (ASSucc lt prev) v (ASSucc ltx ASNil) impossible
allSmallSProp f (ASSucc ltx prevx) = f prevx

notSmallerProp : (LTEq (S x) m -> Void) -> AllSmallerT (x :: xs) m -> Void
notSmallerProp tovoid ASNil impossible
notSmallerProp tovoid (ASSucc lt prev) = tovoid lt

export 
%hint
eitherAllSmallerOrNot : (m:Qubit) -> (v: LVect n Qubit) -> Either (AllSmallerT v m) ((AllSmallerT v m) -> Void)
eitherAllSmallerOrNot  {m} {v = []} = Left ASNil
eitherAllSmallerOrNot  {m} {v = (x::xs)} = case isLTq x m of
  Yes prfLTq => case (eitherAllSmallerOrNot {m = m} {v = xs}) of 
    Left allsmaller => Left $ ASSucc prfLTq allsmaller
    Right notallsmaller => Right $ allSmallSProp notallsmaller
  No notsmaller => Right $ notSmallerProp notsmaller


export  
findProofIsInjectiveTOrNothing : {m:Qubit} -> {v: LVect n Qubit} -> Maybe (IsInjectiveT m v)
findProofIsInjectiveTOrNothing {m} {v} = case (findProofAllDiffOrNothing {v = v}) of 
    Just alldif => case (findProofAllSmallerOrNothing {m = m} {v = v}) of 
        Just allsmaller => Just $ IsInjectiveSucc alldif allsmaller
        Nothing => Nothing
    Nothing => Nothing


notInjIfNotSmallProp : (AllSmallerT v m -> Void) -> IsInjectiveT m v -> Void
notInjIfNotSmallProp tovoid (IsInjectiveSucc alldif allsmaller) = tovoid allsmaller    

notInjIfNotDifProp : (AllDifferentT v -> Void) -> IsInjectiveT m v -> Void
notInjIfNotDifProp tovoid (IsInjectiveSucc alldif allsmaller) = tovoid alldif   


export 
%hint 
eitherIsInjectiveTOrNot : {m:Qubit} -> {v: LVect n Qubit} -> Either (IsInjectiveT m v) ((IsInjectiveT m v) -> Void)
eitherIsInjectiveTOrNot {m} {v} = case (eitherAllDiffOrNot {v = v}) of 
    Left alldif => case (eitherAllSmallerOrNot {m = m} {v = v}) of 
        Left allsmaller => Left $ IsInjectiveSucc alldif allsmaller
        Right notallsmaller => Right $ notInjIfNotSmallProp notallsmaller
    Right notalldiff => Right $ notInjIfNotDifProp notalldiff


export 
%hint
decInj : (m:Qubit) -> (v : LVect n Qubit) -> Dec (IsInjectiveT m v) 
decInj m v = case eitherIsInjectiveTOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 

export   
%hint
decInjHint : {m:Qubit} -> {v : LVect n Qubit} -> Dec (IsInjectiveT m v) 
decInjHint {m} {v} = case eitherIsInjectiveTOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 
