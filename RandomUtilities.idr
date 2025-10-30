module RandomUtilities

import System.Random
import Data.Nat
import Data.Vect
import Data.Vect.Sort
import Data.Vect.Elem
import Decidable.Equality
--import Injection
import Complex
import NatRules
import LinearTypes
import public Data.Linear.Notation
import public Data.Linear.Interface
import System
import Data.Linear
import Lemmas


||| Generate a vector of random doubles
export
randomVect : (n : Nat) -> IO (Vect n Double)
randomVect 0 = pure []
randomVect (S k)  = do
  r <- randomRIO (0,2*pi)
  v <- randomVect k
  pure (r :: v)


{-
------------------------------------------------------------------------------
---------------------------------------------------------------------------
public export
data AllSmallerQ : (v: Vect n Qubit) -> (m:Qubit) -> Type where
    ASQNil  : AllSmallerQ [] m 
    ASQSucc :  LTq x m -> (soFarSmaller: AllSmallerQ xs m)-> AllSmallerQ (x :: xs) m

export
getPrfSmaller : AllSmallerQ v m -> LTq (head v) m
getPrfSmaller ASQNil impossible
getPrfSmaller (ASQSucc prf sfs) = prf

|||Are all the elements in a vector smaller than a given Qubit?
public export 
allSmallerQ : Vect n Qubit -> Qubit -> Type
allSmallerQ v m = AllSmallerQ v m 

export
ifAllSmallThenSubSmall : AllSmallerQ (x::xs) m -> AllSmallerQ xs m
ifAllSmallThenSubSmall (ASQSucc a b) = b

export
plusLTq : {a,b:Qubit} -> (c:Qubit) -> LTq a b -> LTq a (b+c)
plusLTq q prf = rewrite plusZeroRightNeutral b in prf 
plusLTq {a} {b} c prf = lteTransitive prf (lteAddRight b)

export
ifAllSmallThenPlusSmall : {v: Vect k Qubit} -> {m: Qubit} -> (n:Qubit) -> AllSmallerQ v m -> AllSmallerQ v (m+n) 
ifAllSmallThenPlusSmall any ASQNil = ASQNil
ifAllSmallThenPlusSmall Z prf = rewrite plusZeroRightNeutral m in prf 
ifAllSmallThenPlusSmall {v = (x::xs)} {m} (S n) (ASQSucc (lt) prev) =  ASQSucc (plusLTq {a = x} {b = m} (S n) lt) (ifAllSmallThenPlusSmall (S n) prev)


ifAllSmallS : {v: Vect k Qubit} -> {m: Qubit} -> {n : Qubit} -> LTq m n -> AllSmallerQ v m -> AllSmallerQ v n 
ifAllSmallS prf ASQNil = ASQNil
ifAllSmallS {v = (x::xs)} {m} {n} prf (ASQSucc (lt) prev) =  ASQSucc (ltqTransitive lt prf) (ifAllSmallS prf prev)

public export
data IsDifferentQ : (m: Qubit) -> (v: Vect n Qubit) -> Type where
    IsDiffQNil  : IsDifferentQ m []
    IsDiffQSucc : (Either (LTq m x) (LTq x m)) -> (soFarDiff: IsDifferentQ m xs) -> IsDifferentQ m (x :: xs)

export
isDifferentT : Qubit -> Vect n Qubit -> Type
isDifferentT n v = IsDifferentQ n v

export
ifDiffThenSubDiff : IsDifferentQ m (x::xs) -> IsDifferentQ m xs
ifDiffThenSubDiff (IsDiffQSucc a b) = b

export
isDiffToPrf : IsDifferentQ m (x::xs) -> Either (LTq m x) (LTq x m)
isDiffToPrf (IsDiffQSucc a b) = a

public export
data AllDifferentQ : (v: Vect n Qubit) -> Type where
    AllDiffQNil  : AllDifferentQ []
    AllDiffQSucc : IsDifferentQ x xs -> (soFarDiff: AllDifferentQ xs)-> AllDifferentQ (x :: xs)

export
ifAllDiffThenSubDiff : AllDifferentQ (x::xs) -> AllDifferentQ xs
ifAllDiffThenSubDiff (AllDiffQSucc a b) = b


export
allDiffToPrf: AllDifferentQ (x::xs) -> IsDifferentQ x xs
allDiffToPrf (AllDiffQSucc a b) = a


public export
allDifferentT : Vect n Qubit -> Type
allDifferentT v = AllDifferentQ v

public export
data IsInjectiveQ : (m:Qubit) -> (v: Vect n Qubit) -> Type where
    IsInjectiveQSucc : AllDifferentQ v -> AllSmallerQ v m-> IsInjectiveQ m v

public export
isInjectiveT : Qubit -> Vect n Qubit -> Type
isInjectiveT m v = IsInjectiveQ m v

export
getAllSmaller: IsInjectiveQ m v -> AllSmallerQ v m
getAllSmaller (IsInjectiveQSucc prf1 prf2) = prf2

export
getAllDifferent : IsInjectiveQ m v -> AllDifferentQ v
getAllDifferent (IsInjectiveQSucc prf1 prf2) = prf1

export
ifInjectiveThenSubInjective : IsInjectiveQ m (x::xs) -> IsInjectiveQ m xs
ifInjectiveThenSubInjective (IsInjectiveQSucc allDiff allSmall)= IsInjectiveQSucc (ifAllDiffThenSubDiff allDiff) (ifAllSmallThenSubSmall allSmall)

||| Alternative - equality to Void

public export
data IsDifferentDec : (m: Qubit) -> (v: Vect n Qubit) -> Type where
    IsDiffQNilDec  : IsDifferentDec m []
    IsDiffQSuccDec : (m = x -> Void)-> (soFarDiff: IsDifferentDec m xs)-> IsDifferentDec m (x :: xs)

export
isDifferentDec : Qubit -> Vect n Qubit -> Type
isDifferentDec n v = IsDifferentDec n v

export
ifDiffThenSubDiffDec  : IsDifferentDec  m (x::xs) -> IsDifferentDec m xs
ifDiffThenSubDiffDec (IsDiffQSuccDec a b) = b

export
isDiffToPrfDec : IsDifferentDec k (x::xs) -> (k = x -> Void)
isDiffToPrfDec (IsDiffQSuccDec a b) = a

export
eqSymVoid : (k = x -> Void) -> (x = k -> Void)
eqSymVoid kxToVoid Refl = kxToVoid Refl


public export
data AllDifferentDec : (v: Vect n Qubit) -> Type where
    AllDiffQNilDec  : AllDifferentDec []
    AllDiffQSuccDec : IsDifferentDec x xs -> (soFarDiff: AllDifferentDec xs)-> AllDifferentDec (x :: xs)

export
ifAllDiffDecThenSubDiffDec : AllDifferentDec (x::xs) -> AllDifferentDec xs
ifAllDiffDecThenSubDiffDec (AllDiffQSuccDec a b) = b

export
allDiffDecToPrf : AllDifferentDec (x::xs) -> IsDifferentDec x xs
allDiffDecToPrf (AllDiffQSuccDec a b) = a

public export
allDifferentDec : Vect n Qubit -> Type
allDifferentDec v = AllDifferentDec v

public export
data IsInjectiveDec : (m:Qubit) -> (v: Vect n Qubit) -> Type where
    IsInjectiveQSuccDec : AllDifferentDec v -> AllSmallerQ v m -> IsInjectiveDec m v

public export
isInjectiveDec : Qubit -> Vect n Qubit -> Type
isInjectiveDec m v = IsInjectiveDec m v

export
getAllSmallerDec : IsInjectiveDec m v -> AllSmallerQ v m
getAllSmallerDec (IsInjectiveQSuccDec prf1 prf2) = prf2

export
getAllDifferentDec : IsInjectiveDec m v -> AllDifferentDec v
getAllDifferentDec (IsInjectiveQSuccDec prf1 prf2) = prf1

export
ifInjectiveDecThenSubInjectiveDec : IsInjectiveDec m (x::xs) -> IsInjectiveDec m xs
ifInjectiveDecThenSubInjectiveDec (IsInjectiveQSuccDec allDiff allSmall) =
    IsInjectiveQSuccDec (ifAllDiffDecThenSubDiffDec allDiff) (ifAllSmallThenSubSmall allSmall)   


export 
findProofIsDiffOrNothing : (m:Qubit) -> (v: Vect n Qubit) -> Maybe (IsDifferentQ m v)
findProofIsDiffOrNothing m [] = Just IsDiffQNil
findProofIsDiffOrNothing m (x::xs) = case isLTq m x of
   Yes prfLeft => case (findProofIsDiffOrNothing m xs) of 
    Just isdif => Just $ IsDiffQSucc (Left prfLeft) isdif
    Nothing => Nothing
   No prfNo1 => case isLTq x m of
     Yes prfRight => case (findProofIsDiffOrNothing m xs) of 
        Just isdif => Just $ IsDiffQSucc (Right prfRight) isdif
        Nothing => Nothing
     No prfNo2 => Nothing
     _ => Nothing
   _ => Nothing

isDifSProp : (IsDifferentQ m xs -> Void) -> (IsDifferentQ m (x :: xs)) -> Void
isDifSProp IsDiffQNil void IsDiffQNil impossible
isDifSProp (IsDiffQSucc either prev) void IsDiffQNil impossible
isDifSProp (IsDiffQSucc either prev) v (IsDiffQSucc eitherx IsDiffQNil) impossible
isDifSProp f (IsDiffQSucc eitherx prevx) = f prevx

eitherVoid: (left -> Void) -> (right-> Void) -> Either left right -> Void
eitherVoid fleft fright (Left l) = fleft l
eitherVoid fleft fright (Right r) = fright r

eitherVoidThenNotDif : (Either (LTq m x) (LTq x m) -> Void) -> IsDifferentQ (m) (x :: xs) -> Void
eitherVoidThenNotDif feither IsDiffQNil impossible
eitherVoidThenNotDif feither (IsDiffQSucc either prev) = feither either


export 
eitherIsDiffOrNot : (m:Qubit) -> (v: Vect n Qubit) -> Either (IsDifferentQ m v) (IsDifferentQ m v -> Void)
eitherIsDiffOrNot m [] = Left IsDiffQNil
eitherIsDiffOrNot m (x::xs) = 
    case isLTq m x of
        Yes prfLeft => case (eitherIsDiffOrNot m xs) of 
            Left isdif => Left $ IsDiffQSucc (Left prfLeft) isdif
            Right notdif => Right (isDifSProp (notdif))
        No prfNo1 => case isLTq x m of
            Yes prfRight => case (eitherIsDiffOrNot m xs) of 
                Left isdif => Left $ IsDiffQSucc (Right prfRight) isdif
                Right notdif => Right (isDifSProp (notdif))
            No prfNo2 => Right (eitherVoidThenNotDif $ eitherVoid prfNo1 prfNo2)
  

export 
findProofAllDiffOrNothing : {v: Vect n Qubit} -> Maybe (AllDifferentQ v)
findProofAllDiffOrNothing {v = []} = Just AllDiffQNil
findProofAllDiffOrNothing {v = (x::xs)} = case (findProofIsDiffOrNothing x xs) of 
    Just isdif => case (findProofAllDiffOrNothing {v = xs}) of 
        Just alldif => Just $ AllDiffQSucc isdif alldif
        Nothing => Nothing
    Nothing => Nothing

allDifSProp : (AllDifferentQ xs -> Void) -> (AllDifferentQ (x :: xs)) -> Void
allDifSProp AllDiffQNil void AllDiffQNil impossible
allDifSProp (AllDiffQSucc either prev) void AllDiffQNil impossible
allDifSProp (AllDiffQSucc either prev) v (AllDiffQSucc eitherx AllDiffQNil) impossible
allDifSProp f (AllDiffQSucc eitherx prevx) = f prevx

notAllDiffProp : (IsDifferentQ x xs -> Void) -> AllDifferentQ (x :: xs) -> Void
notAllDiffProp tovoid AllDiffQNil impossible
notAllDiffProp tovoid (AllDiffQSucc isdif prev) = tovoid isdif


export 
%hint
eitherAllDiffOrNot  : {v: Vect n Qubit} -> Either (AllDifferentQ v) (AllDifferentQ v -> Void)
eitherAllDiffOrNot  {v = []} = Left AllDiffQNil
eitherAllDiffOrNot {v = (x::xs)} = case (eitherIsDiffOrNot x xs) of 
    Left isdif => case (eitherAllDiffOrNot {v = xs}) of 
        Left alldif => Left (AllDiffQSucc isdif alldif)
        Right notalldif => Right (allDifSProp notalldif)
    Right notalldif => Right (notAllDiffProp (notalldif))


export 
findProofAllSmallerOrNothing : (m:Qubit) -> (v: Vect n Qubit) -> Maybe (AllSmallerQ v m)
findProofAllSmallerOrNothing {m} {v = []} = Just ASQNil
findProofAllSmallerOrNothing {m} {v = (x::xs)} = case isLTq x m of
  Yes prfLTq => case (findProofAllSmallerOrNothing {m = m} {v = xs}) of 
    Just allsmaller => Just $ ASQSucc prfLTq allsmaller
    Nothing => Nothing
  No prfNo1 => Nothing

allSmallSProp : (AllSmallerQ xs m -> Void) -> AllSmallerQ (x :: xs) m -> Void
allSmallSProp ASQNil void ASQNil impossible
allSmallSProp (ASQSucc lt prev) void ASQNil impossible
allSmallSProp (ASQSucc lt prev) v (ASQSucc ltx ASQNil) impossible
allSmallSProp f (ASQSucc ltx prevx) = f prevx

notSmallerProp : (LTq x m -> Void) -> AllSmallerQ (x :: xs) m -> Void
notSmallerProp tovoid ASQNil impossible
notSmallerProp tovoid (ASQSucc lt prev) = tovoid lt

export 
%hint
eitherAllSmallerOrNot : (m:Qubit) -> (v: Vect n Qubit) -> Either (AllSmallerQ v m) ((AllSmallerQ v m) -> Void)
eitherAllSmallerOrNot  {m} {v = []} = Left ASQNil
eitherAllSmallerOrNot  {m} {v = (x::xs)} = case isLTq x m of
  Yes prfLTq => case (eitherAllSmallerOrNot {m = m} {v = xs}) of 
    Left allsmaller => Left $ ASQSucc prfLTq allsmaller
    Right notallsmaller => Right $ allSmallSProp notallsmaller
  No notsmaller => Right $ notSmallerProp notsmaller


export  
findProofIsInjectiveQOrNothing : {m:Qubit} -> {v: Vect n Qubit} -> Maybe (IsInjectiveQ m v)
findProofIsInjectiveQOrNothing {m} {v} = case (findProofAllDiffOrNothing {v = v}) of 
    Just alldif => case (findProofAllSmallerOrNothing {m = m} {v = v}) of 
        Just allsmaller => Just $ IsInjectiveQSucc alldif allsmaller
        Nothing => Nothing
    Nothing => Nothing


notInjIfNotSmallProp : (AllSmallerQ v m -> Void) -> IsInjectiveQ m v -> Void
notInjIfNotSmallProp tovoid (IsInjectiveQSucc alldif allsmaller) = tovoid allsmaller    

notInjIfNotDifProp : (AllDifferentQ v -> Void) -> IsInjectiveQ m v -> Void
notInjIfNotDifProp tovoid (IsInjectiveQSucc alldif allsmaller) = tovoid alldif   


export 
%hint 
eitherIsInjectiveQOrNot : {m:Qubit} -> {v: Vect n Qubit} -> Either (IsInjectiveQ m v) ((IsInjectiveQ m v) -> Void)
eitherIsInjectiveQOrNot {m} {v} = case (eitherAllDiffOrNot {v = v}) of 
    Left alldif => case (eitherAllSmallerOrNot {m = m} {v = v}) of 
        Left allsmaller => Left $ IsInjectiveQSucc alldif allsmaller
        Right notallsmaller => Right $ notInjIfNotSmallProp notallsmaller
    Right notalldiff => Right $ notInjIfNotDifProp notalldiff


export 
%hint
decInjQ : (m:Qubit) -> (v : Vect n Qubit) -> Dec (IsInjectiveQ m v) 
decInjQ m v = case eitherIsInjectiveQOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 

export   
%hint
decInjQHint : {m:Qubit} -> {v : Vect n Qubit} -> Dec (IsInjectiveQ m v) 
decInjQHint {m} {v} = case eitherIsInjectiveQOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 



zeroIsInj : (new: Qubit) -> (lv : Vect Z Qubit) -> IsInjectiveQ new lv
zeroIsInj q [] = IsInjectiveQSucc AllDiffQNil ASQNil

data DTriple : (a : Type) -> (b :Type) -> (p : a -> b -> Type) -> Type where
    MkDTriple : {p : a -> b -> Type} -> (x : a) -> (y : b) ->  p x y -> DTriple a b p 

public export

data UVect : Nat -> Type -> Type where
  UNil : UVect Z Qubit
  Cons : (1 new : Qubit) -> (lv: Vect k Qubit) -> (prf: IsInjectiveQ new lv) -> UVect (S k) Qubit


zeroUtoPrf : (new: Qubit) -> UVect Z Qubit -> (DTriple Qubit (Vect Z Qubit) (IsInjectiveQ))
zeroUtoPrf qubit UNil = MkDTriple qubit [] (zeroIsInj qubit [])

getVandInj: UVect (S k) Qubit -> (DTriple Qubit (Vect k Qubit) (IsInjectiveQ))
getVandInj UNil impossible
getVandInj (Cons new lv prf) = MkDTriple new lv prf

uVtoV : {n:Nat} -> UVect n Qubit -> Vect n Qubit
uVtoV UNil = []
uVtoV {n = S k} (Cons q lv prf) = rewrite sym $ lemmaplusOneRight k in lv ++ [q]

concatSingleR : {i:Nat} -> (1 _ : Vect i Qubit) -> (1 _ : Qubit) -> (Vect (S i) Qubit)
concatSingleR {i=Z} [] q = [q]
concatSingleR {i=i} is q = (rewrite sym $ lemmaplusOneRightHC {n = i} in (LinearTypes.(++) is [q]))

ifAllSmallThenIsDiff : AllSmallerQ v m -> IsDifferentQ m v
ifAllSmallThenIsDiff ASQNil = IsDiffQNil
ifAllSmallThenIsDiff (ASQSucc lt pre) = IsDiffQSucc (Right lt) (ifAllSmallThenIsDiff pre)

newUVect : (k:Nat) -> UVect k Qubit
newUVect Z = UNil
newUVect (S Z) = Cons (MkQubit (Z)) [] (zeroIsInj (MkQubit (Z)) [])
newUVect (S (S j)) =
  let (Cons (MkQubit j) (prevlv) prevprf) = newUVect (S j) in
    case prevlv of 
     [] => ?whatever
     (MkQubit p)::ps => let
      newallsmall = ASQSucc (succBigger {j = j}) (ifAllSmallS (succBigger {j = j}) (getAllSmaller prevprf))
      prevalldiff = (getAllDifferent prevprf) 
      isdiffsofarnew = ifAllSmallThenIsDiff (getAllSmaller prevprf)
      newalldiff = AllDiffQSucc isdiffsofarnew (prevalldiff)
      succprf = (IsInjectiveQSucc newalldiff newallsmall) 
      in Cons (MkQubit (S j)) ((MkQubit j) :: (MkQubit p) ::ps) succprf
-}