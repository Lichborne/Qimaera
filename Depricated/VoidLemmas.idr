--LEMMAS USED BY THE TENSOR FUNCTION (with Void)

-- derive contra from k = S (j + k) 
impossibleEq : (j, k : Nat) -> k = S (j + k) -> Void
impossibleEq j  Z     Refl impossible                              -- 0 ≠ S _
impossibleEq j (S k') eq =
  let
    p1= rewrite plusSuccRightSucc j k' in eq
    p2 = succInjective p1
  in
    impossibleEq j k' p2

||| Giving the implementation outside did not seem to work, so I pulled it inside
export
lemmaDiffSuccPlusEDec : (k : Nat) -> (p : Nat) -> (k  = (S (p + k)) -> Void)
lemmaDiffSuccPlusEDec 0 p eq = absurd eq
lemmaDiffSuccPlusEDec (S k) j eq = let 
      implementation Uninhabited ((S k = S (j + S k))) where
          uninhabited eqn = impossibleEq j k (succInjective (rewrite plusSuccRightSucc j k in eqn))
      in
        absurd (uninhabited (eq))
 
export
isDiffRangeVectDec : (k : Nat) -> (length : Nat) -> (p : Nat) -> IsDifferentDec k (rangeVect (S (p + k)) length)
isDiffRangeVectDec k 0 _ = IsDiffNilDec
isDiffRangeVectDec k (S j) p = IsDiffSuccDec (lemmaDiffSuccPlusEDec k p) (isDiffRangeVectDec k j (S p))

export
allDiffRangeVectDec : (startIndex : Nat) -> (length : Nat) -> AllDifferentDec (rangeVect startIndex length)
allDiffRangeVectDec startIndex 0 = AllDiffNilDec
allDiffRangeVectDec startIndex (S k) = 
  let p1 = isDiffRangeVectDec startIndex k 0
  in AllDiffSuccDec p1 (allDiffRangeVectDec (S startIndex) k)

export
allSmallerRangeVectDec : (startIndex : Nat) -> (length : Nat) -> AllSmallerT (rangeVect startIndex length) (startIndex + length)
allSmallerRangeVectDec startIndex 0 = ASNil
allSmallerRangeVectDec startIndex (S k) = 
  rewrite sym $ plusSuccRightSucc startIndex k in 
    ASSucc (lemmaLTSuccPlus startIndex k) (allSmallerRangeVectDec (S startIndex) k) 

export 
isInjectiveRangeVectDec : (startIndex : Nat) -> (length : Nat) -> IsInjectiveDec (startIndex+length) (rangeVect startIndex length)
isInjectiveRangeVectDec i length = IsInjectiveSuccDec (allDiffRangeVectDec i length) (allSmallerRangeVectDec i length)

export
%hint
lemmaIsDiffGenDec : (m:Nat) -> (v: Vect n Nat) -> IsDifferentDec m v
lemmaIsDiffGenDec m [] = IsDiffNilDec
lemmaIsDiffGenDec m (x::xs) = case decEq m x of
  No prfNo => IsDiffSuccDec (prfNo ) (lemmaIsDiffGenDec m xs)
  Yes prfLeft => assert_total $ idris_crash "There exists no automatic proof that the Vector is Injective"

export 
%hint    
lemmaAllDiffGenDec : {v: Vect n Nat} -> AllDifferentDec v
lemmaAllDiffGenDec {v = []} = AllDiffNilDec
lemmaAllDiffGenDec {v = (x::xs)} = AllDiffSuccDec (lemmaIsDiffGenDec x xs) (lemmaAllDiffGenDec {v = xs})

export 
%hint 
lemmaAllSmallGenDec : (m:Nat) -> (v: Vect n Nat) -> AllSmallerT v m
lemmaAllSmallGenDec {m} {v = []} = ASNil
lemmaAllSmallGenDec {m} {v = (x::xs)} = case isLT x m of
  No prfNo1 =>assert_total $ idris_crash "There exists no automatic proof that the Vector is Injective"
  Yes prfLT => ASSucc prfLT (lemmaAllSmallGenDec {m = m} {v = xs})

export 
%hint 
lemmaIsInjectiveDec : {m:Nat} -> {v: Vect n Nat} -> IsInjectiveDec m v
lemmaIsInjectiveDec {m} {v} = IsInjectiveSuccDec (lemmaAllDiffGenDec {v = v}) (lemmaAllSmallGenDec {m = m} {v = v})

export 
%hint 
lemmaIsInjectiveDecT : {m: Nat -> Nat} -> {v: Nat-> Vect n Nat} -> ({k: Nat} -> IsInjectiveDec (m k) (v k))
lemmaIsInjectiveDecT {m} {v} = IsInjectiveSuccDec (lemmaAllDiffGenDec {v = v k}) (lemmaAllSmallGenDec {m = m k} {v = v k})

export
%hint
implementation {j,k :Nat} -> Uninhabited ((S k = S (j + S k))) where
        uninhabited eqn = impossibleEq j k (succInjective (rewrite plusSuccRightSucc j k in eqn))

export
%hint
implementation Uninhabited (S k = k) where
        uninhabited Refl impossible

export
%hint
implementation Uninhabited (k = S k) where
        uninhabited Refl impossible
                
export
%hint
voidGenLeft : {k : Nat} -> S k = k -> Void
voidGenLeft eq = absurd eq


export
%hint
voidGenRight : {k : Nat} -> k = S k -> Void
voidGenRight eq = absurd eq



---INJ




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

export
eqSymVoid : (k = x -> Void) -> (x = k -> Void)
eqSymVoid kxToVoid Refl = kxToVoid Refl
{-public export
data EitherAnd : (sumType: Either a b) -> Type where
    EitherNil : EitherAnd sumType
    EitherCons : (e : sumType) -> (es: EitherAnd (Left e)) -> EitherAnd sum
-}