module Qubit

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

export
data Qubit : Type where
  MkQubit : (n : Nat) -> Qubit

data QubitExp : Nat -> Type where
  MkQE : (n :Nat) -> QubitExp n

qToNat : Qubit -> Nat
qToNat (MkQubit a) = a  

export
(+) : Qubit -> Qubit -> Qubit 
(+) (MkQubit a) (MkQubit b) = (MkQubit (plus a b))

Injective MkQubit where
  injective Refl = Refl

export
Uninhabited ( MkQubit Z =  MkQubit (S n)) where
  uninhabited Refl impossible

export
Uninhabited ( MkQubit (S n) =  MkQubit (Z))  where
  uninhabited Refl impossible

export
Uninhabited (( MkQubit a =  MkQubit b)) => Uninhabited  (( MkQubit (S a) =  MkQubit (S b))) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
data LTEq  : (a, b : Qubit) -> Type where
  LTEqCons: LTE left right -> LTEq (MkQubit left) (MkQubit right)

public export
Transitive Qubit LTEq where
  transitive (LTEqCons xy) (LTEqCons yz) =
    LTEqCons $ transitive xy yz


toLteqSucc : (LTEq (MkQubit (m)) (MkQubit (n))) -> (LTEq (MkQubit (S m)) (MkQubit (S n)))
toLteqSucc (LTEqCons x) = LTEqCons $ LTESucc x

fromLteqSucc : (LTEq (MkQubit (S m)) (MkQubit (S n))) -> (LTEq (MkQubit (m)) (MkQubit (n)))
fromLteqSucc (LTEqCons x) = LTEqCons $ fromLteSucc x

succNotLTEqzero : Not (LTEq (MkQubit (S n)) (MkQubit Z))
succNotLTEqzero LTEZero impossible

public export
isLTEq : (a, b : Qubit) -> Dec (LTEq a b)
isLTEq (MkQubit Z)  (MkQubit n) = Yes (LTEqCons LTEZero)
isLTEq (MkQubit (S k)) (MkQubit Z) = No (succNotLTEqzero)
isLTEq (MkQubit (S k)) (MkQubit (S j))
    = case isLTEq (MkQubit (k)) (MkQubit j) of
           No contra => No (contra . fromLteqSucc)
           Yes prf => Yes (toLteqSucc prf)


public export
data LTq : Qubit -> Qubit -> Type where 
   LTqCons : LTEq (MkQubit (S left)) (MkQubit right) -> LTq (MkQubit (left)) (MkQubit right)

notltenotlt : (LTEq (MkQubit (S left)) (MkQubit right) -> Void) -> LTq (MkQubit (left)) (MkQubit right) -> Void
notltenotlt tovoid (LTqCons lte) = tovoid lte

public export
isLTq : (l, r : Qubit) -> Dec (LTq l r)
isLTq (MkQubit left) (MkQubit right)= case isLTEq (MkQubit (S left)) (MkQubit right) of 
  Yes prf => Yes (LTqCons prf)
  No notprf => No (notltenotlt notprf)

--public export
--decEqCong : (0 _ : Injective f) => Dec (x = y) -> Dec (f x = f y)
--decEqCong $ Yes prf   = Yes $ cong f prf
--decEqCong $ No contra = No $ \c => contra $ inj f c

public export
DecEq Qubit where
  decEq (MkQubit Z)     (MkQubit Z)  = Yes Refl
  decEq (MkQubit (S n)) (MkQubit (S m)) = decEqCong $ decEq (S n) (S m)
  decEq (MkQubit Z)    (MkQubit (S _)) = No absurd
  decEq (MkQubit (S _)) (MkQubit Z)     = No absurd

public export  
Consumable Qubit where
  consume (MkQubit Z) = ()
  consume (MkQubit (S k)) = ()

public export  
Consumable Nat where
  consume (Z) = ()
  consume ((S k)) = ()

public export 
consLinQ : (Qubit) -> (1_: Vect n Qubit) -> Vect (S n) Qubit
consLinQ (MkQubit Z) [] = [(MkQubit Z)]
consLinQ (MkQubit Z) (x :: xs) = (MkQubit Z) :: x :: xs
consLinQ ((MkQubit (S k))) [] = [MkQubit (S k)]
consLinQ (MkQubit (S k)) (x :: xs) = (MkQubit (S k)) :: x :: xs  

public export
toVectQ : (1 _ : LVect n Qubit) -> (Vect n Qubit)
toVectQ [] = []
toVectQ ((MkQubit k):: xs) = (MkQubit k) `consLinQ` (toVectQ xs)

public export
toLVectQ : (Vect n Nat) -> (LVect n Qubit)
toLVectQ [] = []
toLVectQ (k :: xs) = (MkQubit k) :: (toLVectQ xs)

export
toLVectQQ : (Vect n Qubit) -> (LVect n Qubit)
toLVectQQ [] = []
toLVectQQ (MkQubit k :: xs) = (MkQubit k) :: (toLVectQQ xs)

export
toVectN : (Vect n Qubit) -> (Vect n Nat)
toVectN [] = []
toVectN (MkQubit k :: xs) = (k) :: (toVectN xs)


export
fromVectN : (Vect n Nat) -> (Vect n Qubit)
fromVectN [] = []
fromVectN (k :: xs) = (MkQubit k) :: (fromVectN xs)

public export
Consumable (Vect i elem) where 
    consume [] = ()
    consume (x :: xs) = ()

public export
discardq : (1_ : LVect n Qubit) -> ()
discardq lvect = consume (toVectQ lvect)

public export
unrestrictVec : (1 _ : Vect n Qubit) -> ((Vect n Qubit))
unrestrictVec [] = unrestricted $ MkBang []
unrestrictVec (x :: xs) =  (unrestricted $ MkBang (x)) :: (unrestricted $ MkBang (unrestrictVec xs))

public export
toVectUnr : (1 _ : LVect n Qubit) -> ((Vect n Qubit))
toVectUnr any = unrestrictVec (toVectQ any)

public export
toVectQNonLin : (1_ : Vect n Qubit) -> Pair (Vect n Qubit) (Vect n Qubit)
toVectQNonLin [] = MkPair [] []
toVectQNonLin ((MkQubit k):: xs) = let rest = (toVectQNonLin xs) in MkPair ((MkQubit k) :: (fst rest)) ((MkQubit k) :: (snd rest)) 

public export
toNVect: (Vect i Nat) -> (Vect k Nat) -> (Vect n Nat) -> (Vect n Nat) 
toNVect _ _ [] = []
toNVect [] _ (x::xs) = (x::xs)
toNVect (x::xs) any (y::ys) = case isElem y (x::xs) of 
  No prf => case isElem y any of
    No prf => y :: (toNVect (x::xs) (any) ys)
    Yes prf => x :: (toNVect (x::xs) (x::any) ys)
  Yes prf => x :: (toNVect (xs) (x::any) ys)

public export
toNVectQ: (Vect i Qubit) -> (Vect n Qubit) -> (Vect n Qubit) 
toNVectQ _ [] = []
toNVectQ [] (x::xs) = (x::xs)
toNVectQ xs ys = fromVectN $ toNVect (toVectN xs) [] (toVectN ys)


||| Find an element in a list : used to find the wire of a qubit
public export
listIndex' : {n : Nat} -> Vect n Qubit -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

||| make a neutral (0 to n) qubit vector
public export
makeNeutralVect' : (n:Nat) -> Vect n Qubit
makeNeutralVect' Z = []
makeNeutralVect' (S k) = (MkQubit k) :: makeNeutralVect' k

||| make a basic vector (basically newqubitspointers n but only for vect)
public export
makeNeutralVect : (n:Nat) -> Vect n Qubit
makeNeutralVect k = reverse $ makeNeutralVect' k

||| duplicate a qubit and take the natural number used to constructed out
public export
qubitToNatPair : (1_ : Qubit) -> Pair Qubit Nat
qubitToNatPair (MkQubit q) = ((MkQubit q), q)

public export
distributeDupedLVect : (1 _ : LVect i Qubit) -> LPair (LVect i Qubit) (LVect i Qubit) 
distributeDupedLVect [] = [] # []
distributeDupedLVect (MkQubit k :: xs) = 
  let (q # v) = distributeDupedLVect xs in
  (MkQubit k :: q ) # (MkQubit k :: v)

public export
distributeDupedLVectVect : (1 _ : LVect i Qubit) -> LFstPair (LVect i Qubit) (Vect i Nat) 
distributeDupedLVectVect [] = [] # []
distributeDupedLVectVect (MkQubit k :: xs) = 
  let (q # v) = distributeDupedLVectVect xs in
  (MkQubit k :: q ) # (k :: v)
  

||| this is unsafe in general, but safe for us
export
findInLinQ : {n:Nat} -> (q : Qubit) -> Vect (S n) Qubit -> (Vect n Qubit)
findInLinQ (MkQubit q) [] impossible
findInLinQ {n = Z} (MkQubit q) (MkQubit m :: xs) = []
findInLinQ {n = S r} (MkQubit q) (MkQubit m :: xs) = case decEq q m of
  Yes _ => xs
  No _ => (MkQubit m :: (findInLinQ {n = r} (MkQubit q) xs))
findInLinQ (MkQubit a) (x :: xs) = xs -- this is vacuous, but idris can't figure this out

|||Find the smallest missing in an ordered vector
smallestMissing': (v: Vect n Nat) -> Nat
smallestMissing' [] = Z
smallestMissing' [Z] = S Z 
smallestMissing' [S k] = S (S k)
smallestMissing' (x::y::ys) = case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)

|||Find the smallest missing in an ordered vector
smallestMissing: (v: Vect n Nat) -> Nat
smallestMissing [] = Z
smallestMissing [Z] = S Z 
smallestMissing [S k] = S (S k)
smallestMissing (x::y::ys) = case x of 
  Z => case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)
  (S k) => Z

||| recalculate the counter
public export
reCalculateCounter : {n:Nat} -> (v: Vect n Qubit) -> Nat
reCalculateCounter [] = 0
reCalculateCounter {n = S k} (x::xs) = smallestMissing (sort (toVectN (x::xs)))

||| add the indices of the new qubits to the vector in the SimulatedOp
public export
newQubitsPointers : {n:Nat} -> (p : Nat) -> (counter : Nat) -> (v: Vect n Qubit) -> LFstPair (LVect p Qubit) (Pair (Vect p Qubit) Nat)
newQubitsPointers 0 counter _ = ([] # ([], counter))
newQubitsPointers {n} (S p) counter xs = let newcounter = (reCalculateCounter (MkQubit counter :: xs)) in
  let (q # (v, newcounter)) = newQubitsPointers p newcounter (MkQubit counter :: xs)
  in (MkQubit counter :: q) #  ((MkQubit counter :: v), newcounter)

public export 
newQubitsPointersOld : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersOld 0 _ = ([] # [])
newQubitsPointersOld (S p) counter = 
  let (q # v) = newQubitsPointersOld p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)  

||| add the indices of the new qubits to the vector in the SimulatedOp
public export
newQubitsPointersNoCount : {n:Nat} -> (p : Nat)  -> (v: Vect n Qubit) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersNoCount 0 _ = ([] # ([]))
newQubitsPointersNoCount {n} (S p) xs = let newcounter = (reCalculateCounter (xs)) in
  let (q # v) = newQubitsPointersNoCount p (MkQubit newcounter :: xs)
  in (MkQubit newcounter :: q) #  ((MkQubit newcounter :: v))

||| Used for tests in Main.
public export 
mkQubitV : (from:Nat) -> (i:Nat) -> Vect i Qubit
mkQubitV Z Z = []
mkQubitV (S k) Z = []
mkQubitV Z (S k) = (MkQubit Z :: mkQubitV (S Z) k)     
mkQubitV (S n) (S k) = (MkQubit (S n) :: mkQubitV (S (S n)) k)  


||| Used for tests in Main.
public export 
mkQubitList : (from:Nat) -> (i:Nat) -> LVect i Qubit
mkQubitList Z Z = []
mkQubitList (S k) Z = []
mkQubitList Z (S k) = (MkQubit Z :: mkQubitList (S Z) k)     
mkQubitList (S n) (S k) = (MkQubit (S n) :: mkQubitList (S (S n)) k)  

----LTE transitivity restated from library ----------------------------------
export 
||| `LTE` is transitive frommain library, unimported
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)
-----------------------------------------------------------------------------

lteqTransitive : LTEq n m -> LTEq m p -> LTEq n p
lteqTransitive (LTEqCons (LTEZero)) (LTEqCons (y))= LTEqCons LTEZero
lteqTransitive (LTEqCons  (LTESucc x)) (LTEqCons  (LTESucc y)) = LTEqCons $ LTESucc (lteTransitive x y)

lteqSuccLeft : LTEq (MkQubit (S m)) (MkQubit n) -> LTEq (MkQubit (m)) (MkQubit n)
lteqSuccLeft (LTEqCons  y) = LTEqCons (lteSuccLeft y)

ltqTransitive : LTq x m -> LTq m n -> LTq x n
ltqTransitive (LTqCons lte1) (LTqCons lte2) = LTqCons (lteqTransitive lte1 (lteqSuccLeft lte2))

selfLTE : {x : Nat} -> LTE x x
selfLTE {x = Z} = LTEZero
selfLTE {x = S k} = LTESucc (selfLTE {x = k})

succBigger : {j:Nat} -> LTq (MkQubit j) (MkQubit (S j))
succBigger {j} = LTqCons (LTEqCons (selfLTE))

ltZeroQ : (MkQubit Z) `LTq` (MkQubit (S m))
ltZeroQ = LTqCons $ LTEqCons ltZero


------------------------------------------------------------------------------
---------------------------------------------------------------------------
public export
data AllSmallerQ : (v: Vect n Qubit) -> (m:Qubit) -> Type where
    ASQNil  : AllSmallerQ [] m 
    ASQSucc :  LTq x m -> (soFarSmaller: AllSmallerQ xs m)-> AllSmallerQ (x :: xs) m
{-}
export
getPrfSmaller : AllSmallerQ v m -> LTq (head v) m
getPrfSmaller ASQNil impossible
getPrfSmaller (ASQSucc prf sfs) = prf
-}
|||Are all the elements in a vector smaller than a given Qubit?
public export 
allSmallerQ : Vect n Qubit -> Qubit -> Type
allSmallerQ v m = AllSmallerQ v m 

export
ifAllSmallThenSubSmall : AllSmallerQ (x::xs) m -> AllSmallerQ xs m
ifAllSmallThenSubSmall (ASQSucc a b) = b
{-}
export
plusLTq : {a,b:Qubit} -> (c:Qubit) -> LTq a b -> LTq a (b+c)
plusLTq q prf = rewrite plusZeroRightNeutral b in prf 
plusLTq {a} {b} c prf = lteTransitive prf (lteAddRight b)

export
ifAllSmallThenPlusSmall : {v: Vect k Qubit} -> {m: Qubit} -> (n:Qubit) -> AllSmallerQ v m -> AllSmallerQ v (m+n) 
ifAllSmallThenPlusSmall any ASQNil = ASQNil
ifAllSmallThenPlusSmall Z prf = rewrite plusZeroRightNeutral m in prf 
ifAllSmallThenPlusSmall {v = (x::xs)} {m} (S n) (ASQSucc (lt) prev) =  ASQSucc (plusLTq {a = x} {b = m} (S n) lt) (ifAllSmallThenPlusSmall (S n) prev)
-}

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


{-}
makeUnique : Vect n Qubit -> Vect k Qubit
makeUnique
-}
zeroIsInj : (new: Qubit) -> (lv : Vect Z Qubit) -> IsInjectiveQ new lv
zeroIsInj q [] = IsInjectiveQSucc AllDiffQNil ASQNil

data DTriple : (a : Type) -> (b :Type) -> (p : a -> b -> Type) -> Type where
    MkDTriple : {p : a -> b -> Type} -> (x : a) -> (y : b) ->  p x y -> DTriple a b p 

getFst : DTriple a b p -> a
getFst (MkDTriple x y p) = x

getSnd: DTriple a b p -> b
getSnd (MkDTriple x y p) = y

getTrd : (triple: DTriple a b p) -> p (getFst triple) (getSnd triple)
getTrd (MkDTriple x y p) = p

public export
data UVect : Nat -> Type -> Type where
  UNil : UVect Z Qubit
  UCons : (1 new : Qubit) -> (v: Vect k Qubit) -> (prf: IsInjectiveQ new v) -> UVect k Qubit -> UVect (S k) Qubit

public export  
data ULVectE : Nat -> Type -> Type 

public export
data EachSmallerUL : (1 m:Qubit) -> (1 v: ULVectE n Qubit) -> Type 

data ULVectE : Nat -> Type -> Type where
  ULNilE : ULVectE Z Qubit
  ULConsE : (1 new : Qubit) -> (1 uve : ULVectE k Qubit) -> EachSmallerUL new uve -> ULVectE (S k) Qubit 

data EachSmallerUL : (1 m :Qubit) -> (1 v: ULVectE n Qubit) ->  Type where  
  ESNilUL  : EachSmallerUL m ULNilE
  ESSuccUL :  LTq x m -> (1 soFarSmaller: EachSmallerUL x xs)-> EachSmallerUL m (ULConsE x xs soFarSmaller)

public export
zeroIsEachSmallL: (1 new: Qubit) -> (1 lv : ULVectE Z Qubit) -> EachSmallerUL new lv
zeroIsEachSmallL (MkQubit k) ULNilE = ESNilUL

public export
ifEachSmallSUL : {v: ULVectE k Qubit} -> {m: Qubit} -> {n : Qubit} -> LTq m n -> EachSmallerUL m v -> EachSmallerUL n v
ifEachSmallSUL prf ESNilUL = ESNilUL
ifEachSmallSUL {v = ULConsE x xs prev} {m=m} {n=n} prf (ESSuccUL (lt) prev) =  
        ESSuccUL (ltqTransitive lt prf) (prev)
             


{-}
newULVectE : (k:Nat) -> ULVectE k Qubit
newULVectE Z = UNilE
newULVectE (S Z) = ULConsE (MkQubit (Z)) UNilE (zeroIsAllSmall (MkQubit (Z)) UNilE )
newULVectE (S (S j)) = let (UConWs (MkQubit j) uvprev prfprev) = newULVectE (S j) in
-}
public export
newULVectE : (k:Nat) -> ULVectE k Qubit
newULVectE Z = ULNilE
newULVectE (S Z) = ULConsE (MkQubit (Z)) ULNilE (zeroIsEachSmallL (MkQubit (Z)) ULNilE) 
newULVectE (S (S j)) = let ULConsE (MkQubit (j)) (prevUV) prevPRF = newULVectE (S j) in
  ULConsE (MkQubit (S j)) (ULConsE (MkQubit (j)) (prevUV) prevPRF) (ESSuccUL (succBigger {j = j}) prevPRF)
{-}
Connex Nat LT where
  connex {x = Z} {y = Z} contra = absurd contra
  connex {x = Z} {y = S k} _ = Left $ lemma1LTESucc k
  connex {y = Z} {x = S k} _ = Right $ lemma1LTESucc k
  connex {x = S i} {y = S k} prf =
    case connex $ prf of -- \xy => prf $ cong S xy of
      Left ?jk => Left ?j --$ LTESucc jk
      Right ?kj => Right ?k -- $ LTESucc kj 
    -}

public export
%hint
Uninhabited (S a = S b) => Uninhabited (a = b) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl    

public export  
%hint
Uninhabited (S a = S b) => Uninhabited (S (S a) = S (S b)) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl    

public export
notSEqNotEq: {i:Nat} -> {k : Nat} -> ((S i = S k) -> Void) -> (i = k) -> Void
notSEqNotEq {i} {k} f eq = f (eqSucc i k eq)

public export
ifNeqThenLT : {i:Nat} -> {k:Nat} -> (contra: (Not (i = k))) -> Either (LT i k) (LT k i)
ifNeqThenLT {i = Z} {k = S k} _ = Left $ lemma1LTESucc k
ifNeqThenLT {k = Z} {i = S k} _ = Right $ lemma1LTESucc k
ifNeqThenLT {k = Z} {i = Z} contra = absurd contra 
ifNeqThenLT {i = S i} {k = S k} prf = let eitherSucc = ifNeqThenLT {i = i} {k = k} (notSEqNotEq {i = i} {k = k} prf) in
  case eitherSucc of 
      Left jk => Left $ LTESucc jk
      Right kj => Right $ LTESucc kj 

public export      
%hint
notLTEandGT : LT k i -> (LT (i) (S k) -> Void)
notLTEandGT ltki = LTImpliesNotGTE (LTESucc ltki)

public export
notLTEandGTf : LT k i -> LT (i) (S k) -> Void
notLTEandGTf ltki ltisk = LTImpliesNotGTE (LTESucc ltki) ltisk

public export
ltNeqThenLT : {i:Nat} -> {k:Nat} -> (lt: LT i (S k)) -> (contra: (Not (i = k))) -> LT i k    
ltNeqThenLT lt contra = case ifNeqThenLT contra of 
  Left ltik => ltik
  Right ltki => absurd $ notLTEandGTf ltki lt

public export  
removeElemESM : {m : Qubit} -> EachSmallerUL m (ULConsE x xs soFarSmaller) -> EachSmallerUL m xs

public export
removeElemULV : {k:Nat} -> (i: Nat) -> {auto prf: LT i (S k)} -> (1 _ : ULVectE (S k) Qubit) -> ULVectE k Qubit
removeElemULV {k = Z} i (ULConsE (MkQubit (j)) (ULNilE) prevPRF) = (ULNilE)
removeElemULV i (ULConsE (MkQubit 0) prevUV prevPRF) = prevUV
removeElemULV {k = (S p)} {prf = prfLT} i (ULConsE (MkQubit (S l)) (prevUV) prevPRF) = case decEq i (S p) of
  Yes prfYes => prevUV
  No prfNo => case (removeElemULV {prf = ltNeqThenLT prfLT prfNo} i prevUV) of 
    ULNilE => ULConsE (MkQubit (S l)) ULNilE (zeroIsEachSmallL (MkQubit (S l)) ULNilE) 
    (ULConsE (MkQubit l) removedUV removedPRF) =>
            (ULConsE (MkQubit (S l)) (ULConsE (MkQubit l) removedUV removedPRF) (ESSuccUL (succBigger {j = l}) removedPRF))

removeElemESM (ESSuccUL lt ESNilUL) =  (ESNilUL)
removeElemESM (ESSuccUL lt (ESSuccUL lt2 rest)) = ESSuccUL (ltqTransitive lt2 lt) rest

public export
lteNatThenLTEQ : LTE n m -> LTEq (MkQubit n) (MkQubit m)
lteNatThenLTEQ lte = LTEqCons lte

public export
lteQthenNat: {n,m :Nat} -> LTq (MkQubit n) (MkQubit m) -> LT n m
lteQthenNat (LTqCons (LTEqCons lt)) = lt

public export
addNewElemULV : ULVectE k Qubit -> ULVectE (S k) Qubit
addNewElemULV ULNilE = ULConsE (MkQubit (Z)) ULNilE (zeroIsEachSmallL (MkQubit (Z)) ULNilE) 
addNewElemULV (ULConsE (MkQubit m) ULNilE prevPRF) = case m of 
  Z => (ULConsE (MkQubit (S m)) (ULConsE (MkQubit m) ULNilE prevPRF) (ESSuccUL (succBigger {j = m}) prevPRF))
  S r => (ULConsE (MkQubit (S r)) (ULConsE (MkQubit Z) ULNilE (zeroIsEachSmallL (MkQubit Z) ULNilE) ) (ESSuccUL (ltZeroQ) (zeroIsEachSmallL (MkQubit Z) ULNilE)))
addNewElemULV (ULConsE (MkQubit q) (ULConsE (MkQubit r) prevprevUV prevprevPRF) (ESSuccUL lt prevprevPRF)) = 
  let (ULConsE (MkQubit m) (ULConsE (MkQubit n) matchUV matchPRF) matchPRFm) = addNewElemULV (ULConsE (MkQubit r) prevprevUV prevprevPRF)
  in
    case decEq (S n) m of 
      Yes prfYes => let newprf = ESSuccUL (succBigger {j = n}) matchPRF in
                    (ULConsE (MkQubit (S m)) 
                        (ULConsE (MkQubit (m)) 
                          (ULConsE (MkQubit n) matchUV matchPRF) 
                            (rewrite sym $ prfYes in newprf))
                              (ESSuccUL (succBigger {j = m}) (rewrite sym $ prfYes in newprf)))
      No prfNo => case ifNeqThenLT prfNo of
        Left llt =>
                  (ULConsE (MkQubit m) 
                    (ULConsE (MkQubit (S n)) 
                      (ULConsE (MkQubit n) matchUV matchPRF) 
                        (ESSuccUL (succBigger {j = n}) matchPRF))
                          (ESSuccUL (LTqCons $ lteNatThenLTEQ llt) (ESSuccUL (succBigger {j = n}) matchPRF)))
        Right rlt => let (ESSuccUL lt rest) = matchPRFm in absurd $ notLTEandGTf (rlt) (LTESucc $ lteQthenNat lt) 

public export       
single : (1 _ : Qubit) -> ULVectE 1 Qubit
single (MkQubit k) = (ULConsE (MkQubit k) ULNilE (zeroIsEachSmallL ((MkQubit k)) ULNilE) )

public export
data UVectE : Nat -> Type -> Type 

public export
data EachSmallerU : (m:Qubit) -> (v: UVectE n Qubit) -> Type 

public export
data UVectE : Nat -> Type -> Type where
  UNilE : UVectE Z Qubit
  UConsE : (new : Qubit) -> (uve : UVectE k Qubit) -> EachSmallerU new uve -> UVectE (S k) Qubit 

public export  
data EachSmallerU : (m:Qubit) -> (v: UVectE n Qubit) ->  Type where  
  ESNilU  : EachSmallerU m UNilE
  ESSuccU :  LTq x m -> (soFarSmaller: EachSmallerU x xs)-> EachSmallerU m (UConsE x xs soFarSmaller)

public export  
getEachSmallDep : {k : Nat} -> (uvsk: UVectE (S k) Qubit) -> DTriple Qubit (UVectE k Qubit) (EachSmallerU)
getEachSmallDep UNilE impossible
getEachSmallDep (UConsE new uve esmu) = MkDTriple new uve esmu

public export
zeroIsEachSmall: (new: Qubit) -> (lv : UVectE Z Qubit) -> EachSmallerU new lv
zeroIsEachSmall q UNilE = ESNilU

public export
ifEachSmallSU : {v: UVectE k Qubit} -> {m: Qubit} -> {n : Qubit} -> LTq m n -> EachSmallerU m v -> EachSmallerU n v
ifEachSmallSU prf ESNilU = ESNilU
ifEachSmallSU {v = UConsE x xs prev} {m=m} {n=n} prf (ESSuccU (lt) prev) =  
        ESSuccU (ltqTransitive lt prf) (prev)        

public export
newUVectE : (k:Nat) -> UVectE k Qubit
newUVectE Z = UNilE
newUVectE (S Z) = UConsE (MkQubit (Z)) UNilE (zeroIsEachSmall (MkQubit (Z)) UNilE) 
newUVectE (S (S j)) = let UConsE (MkQubit (j)) (prevUV) prevPRF = newUVectE (S j) in
  UConsE (MkQubit (S j)) (UConsE (MkQubit (j)) (prevUV) prevPRF) (ESSuccU (succBigger {j = j}) prevPRF)

public export  
removeElemE : {m : Qubit} -> EachSmallerU m (UConsE x xs soFarSmaller) -> EachSmallerU m xs

public export
removeElemUV : {k:Nat} -> (i: Nat) -> {auto prf: LT i (S k)} -> UVectE (S k) Qubit -> UVectE k Qubit
removeElemUV {k = Z} i (UConsE (MkQubit (j)) (UNilE) prevPRF) = (UNilE)
removeElemUV i (UConsE (MkQubit 0) prevUV prevPRF) = prevUV
removeElemUV {k = (S p)} {prf = prfLT} i (UConsE (MkQubit (S l)) (prevUV) prevPRF) = case decEq i (S p) of
  Yes prfYes => prevUV
  No prfNo => case (removeElemUV {prf = ltNeqThenLT prfLT prfNo} i prevUV) of 
    UNilE => UConsE (MkQubit (S l)) UNilE (zeroIsEachSmall (MkQubit (S l)) UNilE) 
    (UConsE (MkQubit l) removedUV removedPRF) =>
            (UConsE (MkQubit (S l)) (UConsE (MkQubit l) removedUV removedPRF) (ESSuccU (succBigger {j = l}) removedPRF))

removeElemE (ESSuccU lt ESNilU) = (ESNilU)
removeElemE (ESSuccU lt (ESSuccU lt2 rest)) = ESSuccU (ltqTransitive lt2 lt) rest


--addNewElemUV (addNewElemUV (removeElemUV 2 (removeElemUV 0 (newUVectE 5))))
public export
addNewElemUV : UVectE k Qubit -> UVectE (S k) Qubit
addNewElemUV UNilE = UConsE (MkQubit (Z)) UNilE (zeroIsEachSmall (MkQubit (Z)) UNilE) 
addNewElemUV (UConsE (MkQubit m) UNilE prevPRF) = case m of 
  Z => (UConsE (MkQubit (S m)) (UConsE (MkQubit m) UNilE prevPRF) (ESSuccU (succBigger {j = m}) prevPRF))
  S r => (UConsE (MkQubit (S r)) (UConsE (MkQubit Z) UNilE (zeroIsEachSmall (MkQubit Z) UNilE) ) (ESSuccU (ltZeroQ) (zeroIsEachSmall (MkQubit Z) UNilE)))
addNewElemUV (UConsE (MkQubit q) (UConsE (MkQubit r) prevprevUV prevprevPRF) (ESSuccU lt prevprevPRF)) = 
  let (UConsE (MkQubit m) (UConsE (MkQubit n) matchUV matchPRF) matchPRFm) = addNewElemUV (UConsE (MkQubit r) prevprevUV prevprevPRF)
  in
    case decEq (S n) m of 
      Yes prfYes => let newprf = ESSuccU (succBigger {j = n}) matchPRF in
                    (UConsE (MkQubit (S m)) 
                        (UConsE (MkQubit (m)) 
                          (UConsE (MkQubit n) matchUV matchPRF) 
                            (rewrite sym $ prfYes in newprf))
                              (ESSuccU (succBigger {j = m}) (rewrite sym $ prfYes in newprf)))
      No prfNo => case ifNeqThenLT prfNo of
        Left llt =>
                  (UConsE (MkQubit m) 
                    (UConsE (MkQubit (S n)) 
                      (UConsE (MkQubit n) matchUV matchPRF) 
                        (ESSuccU (succBigger {j = n}) matchPRF))
                          (ESSuccU (LTqCons $ lteNatThenLTEQ llt) (ESSuccU (succBigger {j = n}) matchPRF)))
        Right rlt => let (ESSuccU lt rest) = matchPRFm in absurd $ notLTEandGTf (rlt) (LTESucc $ lteQthenNat lt) 

------------------------------------------------------------------------------------------------------
public export
uLVtoUV : {n:Nat} -> ULVectE n Qubit -> UVectE n Qubit  

public export
esmULtoU : {n:Nat} ->  {lv: ULVectE n Qubit} -> EachSmallerUL m lv -> EachSmallerU m (uLVtoUV lv)
  
uLVtoUV ULNilE = UNilE
uLVtoUV (ULConsE lt prev esm) = (UConsE lt (uLVtoUV prev) (esmULtoU esm))

esmULtoU ESNilUL = ESNilU
esmULtoU (ESSuccUL lt  ESNilUL) = ESSuccU lt (esmULtoU ESNilUL)
esmULtoU (ESSuccUL lt (ESSuccUL lt2 prev)) = --let (ESSuccU lt2 prev) = esmULtoU (ESSuccUL lt2 prev) in
  ESSuccU lt (esmULtoU (ESSuccUL lt2 prev))

export
toVectFromULV : (1_ : ULVectE n Qubit) -> LVect n Qubit
toVectFromULV ULNilE = []
toVectFromULV (ULConsE q prevs prfs) = q :: (toVectFromULV prevs)

export
discardULV : (1_ : ULVectE n Qubit) -> ()
discardULV lvect = consume (toVectQ (toVectFromULV lvect))

------------------------------------------------------------------------------------------------------
public export
uVtoLV : {n:Nat} -> UVectE n Qubit -> ULVectE n Qubit  

public export
esmUtoUL : {n:Nat} ->  {v: UVectE n Qubit} -> EachSmallerU m v -> EachSmallerUL m (uVtoLV v)
  
uVtoLV UNilE = ULNilE
uVtoLV (UConsE lt prev esm) = (ULConsE lt (uVtoLV prev) (esmUtoUL esm))

esmUtoUL ESNilU = ESNilUL
esmUtoUL (ESSuccU lt  ESNilU) = ESSuccUL lt (esmUtoUL ESNilU)
esmUtoUL (ESSuccU lt (ESSuccU lt2 prev)) = --let (ESSuccU lt2 prev) = esmUtoUL (ESSuccUL lt2 prev) in
  ESSuccUL lt (esmUtoUL (ESSuccU lt2 prev))

export
splitLast : {i: Nat} -> {n : Nat} -> (1_ : ULVectE (S i) Qubit) -> (LPair (ULVectE i Qubit) (ULVectE 1 Qubit))
splitLast {i = Z} {n = n} ULNilE impossible
splitLast {i = Z} {n = n}  (ULConsE q ULNilE prevPRF) = ULNilE # (ULConsE q ULNilE prevPRF)
splitLast {i = (S Z)} {n = n} (ULConsE q (ULConsE r ULNilE prevprevPRF) prevPRF)  = (single q) # (ULConsE r ULNilE prevprevPRF)
splitLast {i = (S (S k))} {n = n} qs = (removeElemULV 0 qs) # (ULConsE (MkQubit (Z)) ULNilE (zeroIsEachSmallL (MkQubit (Z)) ULNilE))

------------------------------------------------------------------------------------------------------ 
  
zeroUtoPrf : (new: Qubit) -> UVect Z Qubit -> (DTriple Qubit (Vect Z Qubit) (IsInjectiveQ))
zeroUtoPrf qubit UNil = MkDTriple qubit [] (zeroIsInj qubit [])

getVandInj: UVect (S k) Qubit -> (DTriple Qubit (Vect k Qubit) (IsInjectiveQ))
getVandInj UNil impossible
getVandInj (UCons new v prf uv) = MkDTriple new v prf

uVtoV : {n:Nat} -> UVect n Qubit -> Vect n Qubit
uVtoV UNil = []
uVtoV {n = S k} (UCons q v prf uv) = rewrite sym $ lemmaplusOneRight k in v ++ [q]

ifAllSmallThenIsDiff : AllSmallerQ v m -> IsDifferentQ m v
ifAllSmallThenIsDiff ASQNil = IsDiffQNil
ifAllSmallThenIsDiff (ASQSucc lt pre) = IsDiffQSucc (Right lt) (ifAllSmallThenIsDiff pre)

newUVect : (k:Nat) -> UVect k Qubit
newUVect Z = UNil
newUVect (S Z) = UCons (MkQubit (Z)) [] (zeroIsInj (MkQubit (Z)) [] ) UNil
newUVect (S (S j)) =
  let (UCons (MkQubit j) (prevlv) prevprf uvprev) = newUVect (S j) in
    let
      newallsmall = ASQSucc (succBigger {j = j}) (ifAllSmallS (succBigger {j = j}) (getAllSmaller prevprf))
      prevalldiff = (getAllDifferent prevprf) 
      isdiffsofarnew = ifAllSmallThenIsDiff (getAllSmaller prevprf)
      newalldiff = AllDiffQSucc isdiffsofarnew (prevalldiff)
      succprf = (IsInjectiveQSucc newalldiff newallsmall) 
      in UCons (MkQubit (S j)) ((MkQubit j) :: prevlv) succprf (UCons (MkQubit j) (prevlv) prevprf uvprev)
      
getPrevUV : UVect (S k) Qubit -> UVect k Qubit
getPrevUV (UCons (MkQubit m) [] prevprf uvprev) = uvprev
getPrevUV (UCons (MkQubit m) (p::prev) prevprf uvprev) = uvprev

indexUVSafe : {n:Nat} -> (i: Nat) -> {auto prf: LT i n} -> UVect n Qubit -> Qubit
indexUVSafe _ {prf} UNil = absurd prf
indexUVSafe Z {prf} (UCons (MkQubit m) (prevlv) prevprf uvprev) = MkQubit m
indexUVSafe {n =(S k)} (S j) {prf} (UCons (MkQubit m) (prevlv) prevprf uvprev) = indexUVSafe j uvprev

{-}
indexInvertUVSafe : {n:Nat} -> (i: Nat) -> {auto prf: LT i n} -> UVect n Qubit -> Qubit
indexInvertUVSafe  _ {prf} UNil = absurd prf
indexInvertUVSafe  {n =(S k)} Z {prf} (UCons (MkQubit m) (prevlv) prevprf uvprev) = indexUVSafe k uvprev
indexInvertUVSafe {n =(S k)} (S j) {prf} (UCons (MkQubit m) (prevlv) prevprf uvprev) = indexUVSafe (k - (S j)) (S acc) uvprev
-}--------------------------------------------------------------------------
---------------------------------------------------------------------------
public export
data AllSmallerQLin : (v: LVect n Qubit) -> (m:Qubit) -> Type where
    ASQLinNil  : AllSmallerQLin [] m 
    ASQLinSucc :  LTq x m -> (soFarSmaller: AllSmallerQLin xs m)-> AllSmallerQLin (x :: xs) m

|||Are all the elements in a vector smaller than a given Qubit?
public export 
AllSmallerQLinear : LVect n Qubit -> Qubit -> Type
AllSmallerQLinear v m = AllSmallerQLin v m 

export
ifAllSmallThenSubSmallQLin : AllSmallerQLin (x::xs) m -> AllSmallerQLin xs m
ifAllSmallThenSubSmallQLin (ASQLinSucc a b) = b


ifAllSmallSQLin : {v: LVect k Qubit} -> {m: Qubit} -> {n : Qubit} -> LTq m n -> AllSmallerQLin v m -> AllSmallerQLin v n 
ifAllSmallSQLin prf ASQLinNil = ASQLinNil
ifAllSmallSQLin {v = (x::xs)} {m} {n} prf (ASQLinSucc (lt) prev) =  ASQLinSucc (ltqTransitive lt prf) (ifAllSmallSQLin prf prev)

public export
data IsDifferentQLin : (m: Qubit) -> (v: LVect n Qubit) -> Type where
    IsDiffQLinNil  : IsDifferentQLin m []
    IsDiffQLinSucc : (Either (LTq m x) (LTq x m)) -> (soFarDiff: IsDifferentQLin m xs) -> IsDifferentQLin m (x :: xs)

export
isDifferentQLin : Qubit -> LVect n Qubit -> Type
isDifferentQLin n v = IsDifferentQLin n v

export
ifDiffThenSubDiffQLin : IsDifferentQLin m (x::xs) -> IsDifferentQLin m xs
ifDiffThenSubDiffQLin (IsDiffQLinSucc a b) = b

export
isDiffToPrfQLin : IsDifferentQLin m (x::xs) -> Either (LTq m x) (LTq x m)
isDiffToPrfQLin (IsDiffQLinSucc a b) = a

public export
data AllDifferentQLin : (v: LVect n Qubit) -> Type where
    AllDiffQLinNil  : AllDifferentQLin []
    AllDiffQLinSucc : IsDifferentQLin x xs -> (soFarDiff: AllDifferentQLin xs)-> AllDifferentQLin (x :: xs)

export
ifAllDiffThenSubDiffQLin : AllDifferentQLin (x::xs) -> AllDifferentQLin xs
ifAllDiffThenSubDiffQLin (AllDiffQLinSucc a b) = b


export
allDiffToPrfQLin: AllDifferentQLin (x::xs) -> IsDifferentQLin x xs
allDiffToPrfQLin (AllDiffQLinSucc a b) = a


public export
allDifferentQLin : LVect n Qubit -> Type
allDifferentQLin v = AllDifferentQLin v

public export
data IsInjectiveQLin : (m:Qubit) -> (v: LVect n Qubit) -> Type where
    IsInjectiveQLinSucc : AllDifferentQLin v -> AllSmallerQLin v m-> IsInjectiveQLin m v

public export
isInjectiveQLin : Qubit -> LVect n Qubit -> Type
isInjectiveQLin m v = IsInjectiveQLin m v

export
getAllSmallerQLin: IsInjectiveQLin m v -> AllSmallerQLin v m
getAllSmallerQLin (IsInjectiveQLinSucc prf1 prf2) = prf2

export
getAllDifferentQLin : IsInjectiveQLin m v -> AllDifferentQLin v
getAllDifferentQLin (IsInjectiveQLinSucc prf1 prf2) = prf1

export
ifInjectiveThenSubInjectiveQLin : IsInjectiveQLin m (x::xs) -> IsInjectiveQLin m xs
ifInjectiveThenSubInjectiveQLin (IsInjectiveQLinSucc allDiff allSmall)= IsInjectiveQLinSucc (ifAllDiffThenSubDiffQLin allDiff) (ifAllSmallThenSubSmallQLin allSmall)


export 
findProofIsDiffQLinOrNothing : (m:Qubit) -> (v: LVect n Qubit) -> Maybe (IsDifferentQLin m v)
findProofIsDiffQLinOrNothing m [] = Just IsDiffQLinNil
findProofIsDiffQLinOrNothing m (x::xs) = case isLTq m x of
   Yes prfLeft => case (findProofIsDiffQLinOrNothing m xs) of 
    Just isdif => Just $ IsDiffQLinSucc (Left prfLeft) isdif
    Nothing => Nothing
   No prfNo1 => case isLTq x m of
     Yes prfRight => case (findProofIsDiffQLinOrNothing m xs) of 
        Just isdif => Just $ IsDiffQLinSucc (Right prfRight) isdif
        Nothing => Nothing
     No prfNo2 => Nothing
     _ => Nothing
   _ => Nothing

isDifQLinSProp : (IsDifferentQLin m xs -> Void) -> (IsDifferentQLin m (x :: xs)) -> Void
isDifQLinSProp IsDiffQLinNil void IsDiffQLinNil impossible
isDifQLinSProp (IsDiffQLinSucc either prev) void IsDiffQLinNil impossible
isDifQLinSProp (IsDiffQLinSucc either prev) v (IsDiffQLinSucc eitherx IsDiffQLinNil) impossible
isDifQLinSProp f (IsDiffQLinSucc eitherx prevx) = f prevx

eitherVoidQLin : (left -> Void) -> (right-> Void) -> Either left right -> Void
eitherVoidQLin fleft fright (Left l) = fleft l
eitherVoidQLin fleft fright (Right r) = fright r

eitherVoidThenNotDifQLin : (Either (LTq m x) (LTq x m) -> Void) -> IsDifferentQLin (m) (x :: xs) -> Void
eitherVoidThenNotDifQLin feither IsDiffQLinNil impossible
eitherVoidThenNotDifQLin feither (IsDiffQLinSucc either prev) = feither either


export 
eitherIsDiffQLinOrNot : (m:Qubit) -> (v: LVect n Qubit) -> Either (IsDifferentQLin m v) (IsDifferentQLin m v -> Void)
eitherIsDiffQLinOrNot m [] = Left IsDiffQLinNil
eitherIsDiffQLinOrNot m (x::xs) = 
    case isLTq m x of
        Yes prfLeft => case (eitherIsDiffQLinOrNot m xs) of 
            Left isdif => Left $ IsDiffQLinSucc (Left prfLeft) isdif
            Right notdif => Right (isDifQLinSProp (notdif))
        No prfNo1 => case isLTq x m of
            Yes prfRight => case (eitherIsDiffQLinOrNot m xs) of 
                Left isdif => Left $ IsDiffQLinSucc (Right prfRight) isdif
                Right notdif => Right (isDifQLinSProp (notdif))
            No prfNo2 => Right (eitherVoidThenNotDifQLin $ eitherVoidQLin prfNo1 prfNo2)
  

export 
findProofAllDiffQLinOrNothing : {v: LVect n Qubit} -> Maybe (AllDifferentQLin v)
findProofAllDiffQLinOrNothing {v = []} = Just AllDiffQLinNil
findProofAllDiffQLinOrNothing {v = (x::xs)} = case (findProofIsDiffQLinOrNothing x xs) of 
    Just isdif => case (findProofAllDiffQLinOrNothing {v = xs}) of 
        Just alldif => Just $ AllDiffQLinSucc isdif alldif
        Nothing => Nothing
    Nothing => Nothing

allDifQLinSProp : (AllDifferentQLin xs -> Void) -> (AllDifferentQLin (x :: xs)) -> Void
allDifQLinSProp AllDiffQLinNil void AllDiffQLinNil impossible
allDifQLinSProp (AllDiffQLinSucc either prev) void AllDiffQLinNil impossible
allDifQLinSProp (AllDiffQLinSucc either prev) v (AllDiffQLinSucc eitherx AllDiffQLinNil) impossible
allDifQLinSProp f (AllDiffQLinSucc eitherx prevx) = f prevx

notAllDiffQLinProp : (IsDifferentQLin x xs -> Void) -> AllDifferentQLin (x :: xs) -> Void
notAllDiffQLinProp tovoid AllDiffQLinNil impossible
notAllDiffQLinProp tovoid (AllDiffQLinSucc isdif prev) = tovoid isdif


export 
%hint
eitherAllDiffQLinOrNot  : {v: LVect n Qubit} -> Either (AllDifferentQLin v) (AllDifferentQLin v -> Void)
eitherAllDiffQLinOrNot  {v = []} = Left AllDiffQLinNil
eitherAllDiffQLinOrNot {v = (x::xs)} = case (eitherIsDiffQLinOrNot x xs) of 
    Left isdif => case (eitherAllDiffQLinOrNot {v = xs}) of 
        Left alldif => Left (AllDiffQLinSucc isdif alldif)
        Right notalldif => Right (allDifQLinSProp notalldif)
    Right notalldif => Right (notAllDiffQLinProp (notalldif))


export 
findProofAllSmallerQLinOrNothing  : (m:Qubit) -> (v: LVect n Qubit) -> Maybe (AllSmallerQLin v m)
findProofAllSmallerQLinOrNothing  {m} {v = []} = Just ASQLinNil
findProofAllSmallerQLinOrNothing  {m} {v = (x::xs)} = case isLTq x m of
  Yes prfLTq => case (findProofAllSmallerQLinOrNothing  {m = m} {v = xs}) of 
    Just allsmaller => Just $ ASQLinSucc prfLTq allsmaller
    Nothing => Nothing
  No prfNo1 => Nothing

allSmallQLinSProp : (AllSmallerQLin xs m -> Void) -> AllSmallerQLin (x :: xs) m -> Void
allSmallQLinSProp ASQLinNil void ASQLinNil impossible
allSmallQLinSProp (ASQLinSucc lt prev) void ASQLinNil impossible
allSmallQLinSProp (ASQLinSucc lt prev) v (ASQLinSucc ltx ASQLinNil) impossible
allSmallQLinSProp f (ASQLinSucc ltx prevx) = f prevx

notSmallerQLinProp : (LTq x m -> Void) -> AllSmallerQLin (x :: xs) m -> Void
notSmallerQLinProp tovoid ASQLinNil impossible
notSmallerQLinProp tovoid (ASQLinSucc lt prev) = tovoid lt

export 
%hint
eitherAllSmallerQLinOrNot : (m:Qubit) -> (v: LVect n Qubit) -> Either (AllSmallerQLin v m) ((AllSmallerQLin v m) -> Void)
eitherAllSmallerQLinOrNot  {m} {v = []} = Left ASQLinNil
eitherAllSmallerQLinOrNot  {m} {v = (x::xs)} = case isLTq x m of
  Yes prfLTq => case (eitherAllSmallerQLinOrNot {m = m} {v = xs}) of 
    Left allsmaller => Left $ ASQLinSucc prfLTq allsmaller
    Right notallsmaller => Right $ allSmallQLinSProp notallsmaller
  No notsmaller => Right $ notSmallerQLinProp notsmaller


export  
findProofIsInjectiveQLinOrNothing : {m:Qubit} -> {v: LVect n Qubit} -> Maybe (IsInjectiveQLin m v)
findProofIsInjectiveQLinOrNothing {m} {v} = case (findProofAllDiffQLinOrNothing {v = v}) of 
    Just alldif => case (findProofAllSmallerQLinOrNothing  {m = m} {v = v}) of 
        Just allsmaller => Just $ IsInjectiveQLinSucc alldif allsmaller
        Nothing => Nothing
    Nothing => Nothing


notInjIfNotSmallQLinProp : (AllSmallerQLin v m -> Void) -> IsInjectiveQLin m v -> Void
notInjIfNotSmallQLinProp tovoid (IsInjectiveQLinSucc alldif allsmaller) = tovoid allsmaller    

notInjIfNotDifQLinProp : (AllDifferentQLin v -> Void) -> IsInjectiveQLin m v -> Void
notInjIfNotDifQLinProp tovoid (IsInjectiveQLinSucc alldif allsmaller) = tovoid alldif   


export 
%hint 
eitherIsInjectiveQLinOrNot : {m:Qubit} -> {v: LVect n Qubit} -> Either (IsInjectiveQLin m v) ((IsInjectiveQLin m v) -> Void)
eitherIsInjectiveQLinOrNot {m} {v} = case (eitherAllDiffQLinOrNot {v = v}) of 
    Left alldif => case (eitherAllSmallerQLinOrNot {m = m} {v = v}) of 
        Left allsmaller => Left $ IsInjectiveQLinSucc alldif allsmaller
        Right notallsmaller => Right $ notInjIfNotSmallQLinProp notallsmaller
    Right notalldiff => Right $ notInjIfNotDifQLinProp notalldiff


export 
%hint
decInjQLin : (m:Qubit) -> (v : LVect n Qubit) -> Dec (IsInjectiveQLin m v) 
decInjQLin m v = case eitherIsInjectiveQLinOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 

export   
%hint
decInjQLinHint : {m:Qubit} -> {v : LVect n Qubit} -> Dec (IsInjectiveQLin m v) 
decInjQLinHint {m} {v} = case eitherIsInjectiveQLinOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 


{-}
makeUnique : LVect n Qubit -> LVect k Qubit
makeUnique
-}
zeroIsInjQLin : (new: Qubit) -> (lv : LVect Z Qubit) -> IsInjectiveQLin new lv
zeroIsInjQLin q [] = IsInjectiveQLinSucc AllDiffQLinNil ASQLinNil

public export
data ULVect : Nat -> Type -> Type where
  ULNil : ULVect Z Qubit
  ULCons : (1 new : Qubit) -> (lv: LVect k Qubit) -> (prf: IsInjectiveQLin new lv) -> ULVect (S k) Qubit


zeroULtoPrf : (new: Qubit) -> ULVect Z Qubit -> (DTriple Qubit (LVect Z Qubit) (IsInjectiveQLin))
zeroULtoPrf qubit ULNil = MkDTriple qubit [] (zeroIsInjQLin qubit [])

getLVandInj: ULVect (S k) Qubit -> (DTriple Qubit (LVect k Qubit) (IsInjectiveQLin))
getLVandInj ULNil impossible
getLVandInj (ULCons new lv prf) = MkDTriple new lv prf

uLVtoLV : {n:Nat} -> ULVect n Qubit -> LVect n Qubit
uLVtoLV ULNil = []
uLVtoLV {n = S k} (ULCons q lv prf) = rewrite sym $ lemmaplusOneRight k in lv ++ [q]

concatSingleRLV : {i:Nat} -> (1 _ : LVect i Qubit) -> (1 _ : Qubit) -> (LVect (S i) Qubit)
concatSingleRLV {i=Z} [] q = [q]
concatSingleRLV {i=i} is q = (rewrite sym $ lemmaplusOneRightHC {n = i} in (LinearTypes.(++) is [q]))

ifAllSmallThenIsDiffQLin : AllSmallerQLin v m -> IsDifferentQLin m v
ifAllSmallThenIsDiffQLin ASQLinNil = IsDiffQLinNil
ifAllSmallThenIsDiffQLin (ASQLinSucc lt pre) = IsDiffQLinSucc (Right lt) (ifAllSmallThenIsDiffQLin pre)

newULVect : (k:Nat) -> ULVect k Qubit
newULVect Z = ULNil
newULVect (S Z) = ULCons (MkQubit (Z)) [] (zeroIsInjQLin (MkQubit (Z)) [])
newULVect (S (S j)) =
  let (ULCons (MkQubit j) (prevlv) prevprf) = newULVect (S j) in
    let
      newallsmall = ASQLinSucc (succBigger {j = j}) (ifAllSmallSQLin (succBigger {j = j}) (getAllSmallerQLin prevprf))
      prevalldiff = (getAllDifferentQLin prevprf) 
      isdiffsofarnew = ifAllSmallThenIsDiffQLin (getAllSmallerQLin prevprf)
      newalldiff = AllDiffQLinSucc isdiffsofarnew (prevalldiff)
      succprf = (IsInjectiveQLinSucc newalldiff newallsmall) 
      in ULCons (MkQubit (S j)) ((MkQubit j) :: prevlv) succprf


-------------------------------------------------------------------------------------





{-}
public export
data AllDifferentQLin : (v: LVect n Qubit) -> Type where
    AllDiffQLinNil  : AllDifferentQLin []
    AllDiffQLinSucc : IsDifferentQLin x xs -> (soFarDiff: AllDifferentQLin xs)-> AllDifferentQLin (x :: xs)


    data IsDifferentQLin : (m: Qubit) -> (v: LVect n Qubit) -> Type where
    IsDiffQLinNil  : IsDifferentQLin m []
    IsDiffQLinSucc : (Either (LTq m x) (LTq x m)) -> (soFarDiff: IsDifferentQLin m xs) -> IsDifferentQLin m (x :: xs)

   
public export
data IsInjectiveDec : (m:Qubit) -> (v: LVect n Qubit) -> Type where
    IsInjectiveQLinSuccDec : AllDifferentDec v -> AllSmallerQLin v m -> IsInjectiveDec m v

-}