module QuantumOp

import Data.Vect
import Data.Vect.Sort
import Data.Vect.Elem
import Data.Nat
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import System.Random
import Lemmas
import QStateT
import Control.Linear.LIO
import LinearTypes
import UnitaryLinear
import UStateT
import Control.Linear.LIO
import UnitaryNoPrf

||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.
export
data Qubit : Type where
  MkQubit : (n : Nat) -> Qubit

public export 
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} -> 
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a user-implemented unitary circuit to the Qubits specified by the Vect argument
  ||| since t n must implement unitaries, it works perfectly here.
  ||| liner in ownUnitary because this way results of "run" can be used
  applyUnitaryOwn : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1 ownUnitary : t i) -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single Qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure [q1]

  ||| Apply a P gate to a single Qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure [q1]

  ||| Apply the CNOT gate to a pair of Qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1::q2::[])
  
  ||| apply a controlled version of a UStateT built using the interface
  ||| since there is a control we have to take from n, the UStateT used at most has n (if i = n) qubits 
  ||| i.e. it is one qubit smaller than the controlled version, which is therefore a larger UStateT
  ||| This will usually be fulfulled automatically by construction
  applyControlledAbs: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (t n) (t n) (LVect i Qubit))      
                   -> UStateT (t (S n)) (t (S n)) (LVect (S i) Qubit)

  ||| Abstract split application: helps with constructing circuits with parallel applications recursively (i.e. tensoring)
  applyParallel: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (t n) (t n) ((LVect i Qubit)))
                        -> (1_ : UStateT (t n) (t n) ((LVect j Qubit))) -> UStateT (t n) (t n) (LVect (i + j) Qubit)
                        
  ||| Find the adjoint operation
  adjointUST: (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (UStateT (t n) (t n) (LVect i Qubit))

  ||| sequence to the end
  run :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit) ) -> (LPair (t n) (LVect i Qubit))

  ||| This needs us to be able to consume the LVect of Qubits, which requires the internal workings of qubits
  ||| to which only QuantumOp has access, and it would be a circular import here. Thus, concrete implementations
  ||| need to define this themselves
  exportSelf :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (t n)

  --------------------- Split Computation and Accompanying Utilities (Useful for some definitions) -------------------------

  |||recombine split computation. This is raised in to UnitaryOp so that idris can see that appropriate conditions are fulfilled
  reCombine : {i:Nat} -> {j:Nat} ->  {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect j Qubit) -> UStateT (t n) (t n) (LVect (i+j) Qubit)
  reCombine {i=i} is js =  pure $ LinearTypes.(++) is js  


  ||| Abstract recombination. Helps with applying a split-computed unitary in QuantumOp
  reCombineAbs : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))) 
                -> UStateT (t n) (t n) (LVect (i + j) Qubit)

  ||| Apply the controlled version of a unitary. Implementations assume control goes at head of lvect list
  applyControlWithSplitLVects : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
                            -> UStateT (t (S n)) (t (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))


------------- OTHER UTILITIES ------------
||| WHILE NOT STRICTLY A PART OF THE INTERFACE
||| IT IS HIGHLY RECOMMENDED THAT THESE 
||| UTILIZED, AS THEY MAKE LIFE A LOT EASIER
------------------------------------------

||| for exporting an instance opf the Unitary algebraic datatype based on the unitary build inside UStateT
||| this is not in general doable, as it depends on the structure of the specific t n and whether it can be translated into 
||| a value of Unitary n, because the proofs are necessary to build an instance of the type
export
exportUnitary : UnitaryOp t => {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (Unitary n)

||| SWAP registers in parsing; an exchange of "wires", easy to make conditional 
export                           
swapRegistersSplit : UnitaryOp t => {i:Nat} -> {j:Nat}  -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect j Qubit) -> UStateT (t n) (t n) (LPair (LVect j Qubit) (LVect i Qubit))
swapRegistersSplit qs rs = pure $ rs # qs

||| SWAP registers in parsing; an exchange of "wires", easy to make conditional 
export                           
swapRegistersSplitEq : UnitaryOp t =>  {i:Nat}  -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect i Qubit))
swapRegistersSplitEq qs rs = pure $ rs # qs

|||recombine split computation, adding one qubit to the end
export
reCombineSingleR :UnitaryOp t =>  {i:Nat} -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
reCombineSingleR {i=Z} [] q =  pure $ [q]
reCombineSingleR {i=i} is q =  pure $ (rewrite sym $ lemmaplusOneRightHC {n = i} in (LinearTypes.(++) is [q]))

||| recombine split computation, adding one qubit to the beginning
export
reCombineSingleL : UnitaryOp t => {i:Nat}  -> {n : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
reCombineSingleL {i=Z} q [] =  pure $ [q]
reCombineSingleL {i=i} q is = pure $ (q :: is)

----------------Optionally definable functions ---------------
||| These are patterns for functions that are useful/helpful to 
||| define in concrete implementations, but are not part of the
||| interface.

||| Apply a user-implemented unitary circuit to the Qubits specified by the Vect argument  
||| This is essentially the same as just sequencing normally, and is mostly only representationally helpful     
export  
applyUnitaryAbs: UnitaryOp t => {n : Nat} -> {i : Nat} -> (1_ : UStateT (t n) (t n) (LVect i Qubit))      
                  -> UStateT (t n) (t n) (LVect i Qubit)


||| sequence to the end with split computation
export
runSplit : UnitaryOp t =>  {i : Nat} -> {j:Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)) ) 
            -> (LPair (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
    
||| Abstract split application: Convenience function for avoiding proofs when dealing with multiple qubit list inputs/ancillae
export
applyWithSplitLVects : UnitaryOp t =>   {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
                        -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))

-------------------------------------------------------------------------------------------------------------
                      
%hint
export
singleQubit : (1 _ : LVect 1 Qubit)-> Qubit
singleQubit [q] = q

public export total
splitFirstUtil : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect 1 Qubit) (LVect i Qubit))
splitFirstUtil {i = Z} [] impossible
splitFirstUtil {i = Z} [as] = pure $ [as] # []
splitFirstUtil {i = (S Z)} [a,b] = pure $ [a] # [b]
splitFirstUtil {i = (S (S k))} (a::as) = do
    pure $ [a] # (as)

|||get the First qubit from a list of qubits
public export total
splitLastUtil : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect 1 Qubit))
splitLastUtil {i = Z} {n = n} [] impossible
splitLastUtil {i = Z} {n = n} [as] = pure $ [] # [as]
splitLastUtil {i = (S Z)} {n = n} [a,b] = pure $ [a] # [b]
splitLastUtil {i = (S (S k))} {n = n} (a::as) = do
    as # last <- splitLastUtil (as)
    pure $ (a :: as) # last
    
||| split qubits at index. careful with proofs 
public export
splitQubitsAt : UnitaryOp t => {i: Nat} -> {n : Nat} -> (k: Nat) -> {auto prf: LT k i} -> (1_ : LVect i Qubit) 
                            -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect (minus i k) Qubit))
splitQubitsAt k [] = absurd prf
splitQubitsAt 0 any  = pure $ [] # (rewrite minusZeroRight i in any)
splitQubitsAt (S k) (a::as) = do
    as # ass <- splitQubitsAt k (as)
    pure $ ((a :: as)) # ass


||| split qubits at index
public export
splitQubitsInto : UnitaryOp t => {i: Nat} -> {n : Nat} -> (k: Nat) -> (r:Nat) -> {auto prf: k + r = i} -> (1_ : LVect i Qubit) 
                            -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect r Qubit))
splitQubitsInto 0 0 [] = pure $ [] # []
splitQubitsInto 0 0 (a::as) impossible
splitQubitsInto {prf} 0 r any = (pure $ [] # (rewrite prf in any))
splitQubitsInto k 0 any = pure $ (rewrite sym $ plusZeroRightNeutral k in (rewrite prf in any)) # []
splitQubitsInto {prf = prf} {i = S h} (S k) (S r) (a::as) = do
    as # ass <- splitQubitsInto {prf = succInjective (rewrite plusSuccLeftSucc (k) (S r) in prf)}k (S r) (as)
    pure $ ((a :: as)) # ass

public export    
splitLVinto : (n : Nat) -> (k: Nat) -> (1_ : LVect (n + k) Qubit) 
                            -> (LPair (LVect n Qubit) (LVect k Qubit))
splitLVinto  0 0 [] = [] # []
splitLVinto 0 0 (a::as) impossible
splitLVinto  0 k any = [] # any
splitLVinto  n 0 any = (rewrite sym $ plusZeroRightNeutral n in any) # []
splitLVinto (S m) (S r) (a::as) = let as # ass = splitLVinto m (S r) (as) in (a::as) # ass


||| Find an element in a list : used to find the wire of a qubit
export
listIndex' : {n : Nat} -> Vect n Qubit -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

||| The QuantumOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of qubits it contains.
public export
interface QuantumOp (0 t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  newQubits : (p : Nat) -> QStateT (t n) (t (n+p)) (LVect p Qubit)
  newQubits Z     = rewrite plusZeroRightNeutral n in pure []
  newQubits (S k) = rewrite lemmaPlusSRight n k in do
    q <- newQubit
    qs <- newQubits k
    pure (q :: qs)

  ||| Prepare a single new qubit in state |0>
  newQubit : QStateT (t n) (t (S n)) Qubit
  newQubit = rewrite sym $ lemmaplusOneRight n in do
    [q] <- newQubits 1
    pure q
  
  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUST : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LVect i Qubit)) -> QStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a unitary directly; kept around for convenience
  applyUnitaryDirectly : {n : Nat} -> {i : Nat} -> Unitary i -> (1_ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)

  ||| Apply Hadamard to specified qubit
  applyHQ: UnitaryOp t => {n : Nat} -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 1 Qubit)
  applyHQ q = do
              q <- applyUST {t = t} (applyH {t = t} {n = n } (q))
              pure q
  
  ||| Apply Hadamard to specified qubit
  applyPQ: UnitaryOp t => {n : Nat} -> (d:Double) -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 1 Qubit)
  applyPQ d q = do
              q <- applyUST {t = t} (applyP d {t = t} {n = n } (q))
              pure q

  ||| Apply  CNOT with specified contorl and target
  applyCNOTQ: UnitaryOp t => {n : Nat} -> (1_ : Qubit) -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 2 Qubit)
  applyCNOTQ c q = do
              cq <- applyUST {t = t} (applyCNOT {t = t} {n = n } c (q))
              pure cq

  ||| Measure some qubits in a quantum state
  measure : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (t (i + n)) (t n) (Vect i Bool)
  
  ||| Measure only one qubit
  measureQubit : {n : Nat} -> (1 _ : Qubit) -> QStateT (t (S n)) (t n) Bool
  measureQubit q = do
    [b] <- measure [q]
    pure b
  ||| Same as measure, but with an initial state of n + i instead of i + n qubits to help with theorem proving in some cases
  -- export
  -- measure2 : {n : Nat} -> {i : Nat} -> (LVect i Qubit) -> QStateT (t (n + i)) (t n) (Vect i Bool)
  -- measure2 v = rewrite plusCommutative n i in measure v

  ||| Measure all qubits in a quantum state
  ||| Because of a bug in Idris2, we use the implementation below.
  ||| However, the implementation commented out is preferable if the bug gets fixed.
  measureAll : {n : Nat} -> (1 _ : LVect n Qubit) -> QStateT (t n) (t 0) (Vect n Bool)
  measureAll []        = pure []
  measureAll (q :: qs) = do
    b <- measureQubit q
    bs <- measureAll qs
    pure (b `consLin` bs)
  --measureAll qs = rewrite sym $ plusZeroRightNeutral n in measure qs
                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  runQ : {n:Nat} -> QStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)

----- Qubit utilities, functions, and proofs----
private
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

export
data LTEq  : (a, b : Qubit) -> Type where
  LTEqCons: LTE left right -> LTEq (MkQubit left) (MkQubit right)

export
Transitive Qubit LTEq where
  transitive (LTEqCons xy) (LTEqCons yz) =
    LTEqCons $ transitive xy yz


toLteqSucc : (LTEq (MkQubit (m)) (MkQubit (n))) -> (LTEq (MkQubit (S m)) (MkQubit (S n)))
toLteqSucc (LTEqCons x) = LTEqCons $ LTESucc x

fromLteqSucc : (LTEq (MkQubit (S m)) (MkQubit (S n))) -> (LTEq (MkQubit (m)) (MkQubit (n)))
fromLteqSucc (LTEqCons x) = LTEqCons $ fromLteSucc x

succNotLTEqzero : Not (LTEq (MkQubit (S n)) (MkQubit Z))
succNotLTEqzero LTEZero impossible

export
isLTEq : (a, b : Qubit) -> Dec (LTEq a b)
isLTEq (MkQubit Z)  (MkQubit n) = Yes (LTEqCons LTEZero)
isLTEq (MkQubit (S k)) (MkQubit Z) = No (succNotLTEqzero)
isLTEq (MkQubit (S k)) (MkQubit (S j))
    = case isLTEq (MkQubit (k)) (MkQubit j) of
           No contra => No (contra . fromLteqSucc)
           Yes prf => Yes (toLteqSucc prf)


export
data LTq : Qubit -> Qubit -> Type where 
   LTqCons : LTEq (MkQubit (S left)) (MkQubit right) -> LTq (MkQubit (left)) (MkQubit right)

notltenotlt : (LTEq (MkQubit (S left)) (MkQubit right) -> Void) -> LTq (MkQubit (left)) (MkQubit right) -> Void
notltenotlt tovoid (LTqCons lte) = tovoid lte

export
isLTq : (l, r : Qubit) -> Dec (LTq l r)
isLTq (MkQubit left) (MkQubit right)= case isLTEq (MkQubit (S left)) (MkQubit right) of 
  Yes prf => Yes (LTqCons prf)
  No notprf => No (notltenotlt notprf)

--export
--decEqCong : (0 _ : Injective f) => Dec (x = y) -> Dec (f x = f y)
--decEqCong $ Yes prf   = Yes $ cong f prf
--decEqCong $ No contra = No $ \c => contra $ inj f c

export
DecEq Qubit where
  decEq (MkQubit Z)     (MkQubit Z)  = Yes Refl
  decEq (MkQubit (S n)) (MkQubit (S m)) = decEqCong $ decEq (S n) (S m)
  decEq (MkQubit Z)    (MkQubit (S _)) = No absurd
  decEq (MkQubit (S _)) (MkQubit Z)     = No absurd

export  
Consumable Qubit where
  consume (MkQubit Z) = ()
  consume (MkQubit (S k)) = ()

export  
Consumable Nat where
  consume (Z) = ()
  consume ((S k)) = ()

export 
consLinQ : (Qubit) -> (1_: Vect n Qubit) -> Vect (S n) Qubit
consLinQ (MkQubit Z) [] = [(MkQubit Z)]
consLinQ (MkQubit Z) (x :: xs) = (MkQubit Z) :: x :: xs
consLinQ ((MkQubit (S k))) [] = [MkQubit (S k)]
consLinQ (MkQubit (S k)) (x :: xs) = (MkQubit (S k)) :: x :: xs  

export
toVectQ : (1 _ : LVect n Qubit) -> (Vect n Qubit)
toVectQ [] = []
toVectQ ((MkQubit k):: xs) = (MkQubit k) `consLinQ` (toVectQ xs)

export
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

export
Consumable (Vect i elem) where 
    consume [] = ()
    consume (x :: xs) = ()

export
discardq : (1_ : LVect n Qubit) -> ()
discardq lvect = consume (toVectQ lvect)

export
unrestrictVec : (1 _ : Vect n Qubit) -> ((Vect n Qubit))
unrestrictVec [] = unrestricted $ MkBang []
unrestrictVec (x :: xs) =  (unrestricted $ MkBang (x)) :: (unrestricted $ MkBang (unrestrictVec xs))

export
toVectUnr : (1 _ : LVect n Qubit) -> ((Vect n Qubit))
toVectUnr any = unrestrictVec (toVectQ any)

export
toVectQNonLin : (1_ : Vect n Qubit) -> Pair (Vect n Qubit) (Vect n Qubit)
toVectQNonLin [] = MkPair [] []
toVectQNonLin ((MkQubit k):: xs) = let rest = (toVectQNonLin xs) in MkPair ((MkQubit k) :: (fst rest)) ((MkQubit k) :: (snd rest)) 

export
toNVect: (Vect i Nat) -> (Vect k Nat) -> (Vect n Nat) -> (Vect n Nat) 
toNVect _ _ [] = []
toNVect [] _ (x::xs) = (x::xs)
toNVect (x::xs) any (y::ys) = case isElem y (x::xs) of 
  No prf => case isElem y any of
    No prf => y :: (toNVect (x::xs) (any) ys)
    Yes prf => x :: (toNVect (x::xs) (x::any) ys)
  Yes prf => x :: (toNVect (xs) (x::any) ys)

export
toNVectQ: (Vect i Qubit) -> (Vect n Qubit) -> (Vect n Qubit) 
toNVectQ _ [] = []
toNVectQ [] (x::xs) = (x::xs)
toNVectQ xs ys = fromVectN $ toNVect (toVectN xs) [] (toVectN ys)

||| Remove an element at a given index in the vector
public export
removeElem : {n : Nat} -> Vect (S n) Qubit -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k

||| make a neutral (0 to n) qubit vector
export
makeNeutralVect' : (n:Nat) -> Vect n Qubit
makeNeutralVect' Z = []
makeNeutralVect' (S k) = (MkQubit k) :: makeNeutralVect' k

||| make a basic vector (basically newqubitspointers n but only for vect)
export
makeNeutralVect : (n:Nat) -> Vect n Qubit
makeNeutralVect k = reverse $ makeNeutralVect' k

||| duplicate a qubit and take the natural number used to constructed out
export
qubitToNatPair : (1_ : Qubit) -> Pair Qubit Nat 
qubitToNatPair (MkQubit q) = ((MkQubit q), q)

export
distributeDupedLVect : (1 _ : LVect i Qubit) -> LPair (LVect i Qubit) (LVect i Qubit) 
distributeDupedLVect [] = [] # []
distributeDupedLVect (MkQubit k :: xs) = 
  let (q # v) = distributeDupedLVect xs in
  (MkQubit k :: q ) # (MkQubit k :: v)

export
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
export
smallestMissing': (v: Vect n Nat) -> Nat
smallestMissing' [] = Z
smallestMissing' [Z] = S Z 
smallestMissing' [S k] = S (S k)
smallestMissing' (x::y::ys) = case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)
      
|||Find the smallest missing in an ordered vector
export
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
export
reCalculateCounter : {n:Nat} -> (v: Vect n Qubit) -> Nat
reCalculateCounter [] = 0
reCalculateCounter {n = S k} (x::xs) = smallestMissing (sort (toVectN (x::xs)))

||| add the indices of the new qubits to the vector in the SimulatedOp
private
newQubitsPointers : {n:Nat} -> (p : Nat) -> (counter : Nat) -> (v: Vect n Qubit) -> LFstPair (LVect p Qubit) (Pair (Vect p Qubit) Nat)
newQubitsPointers 0 counter _ = ([] # ([], counter))
newQubitsPointers {n} (S p) counter xs = let newcounter = (reCalculateCounter (MkQubit counter :: xs)) in
  let (q # (v, newcounter)) = newQubitsPointers p newcounter (MkQubit counter :: xs)
  in (MkQubit counter :: q) #  ((MkQubit counter :: v), newcounter)

private
newQubitsPointersOld : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersOld 0 _ = ([] # [])
newQubitsPointersOld (S p) counter = 
  let (q # v) = newQubitsPointersOld p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)  

||| add the indices of the new qubits to the vector in the SimulatedOp
private
newQubitsPointersNoCount : {n:Nat} -> (p : Nat)  -> (v: Vect n Qubit) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersNoCount 0 _ = ([] # ([]))
newQubitsPointersNoCount {n} (S p) xs = let newcounter = (reCalculateCounter (xs)) in
  let (q # v) = newQubitsPointersNoCount p (MkQubit newcounter :: xs)
  in (MkQubit newcounter :: q) #  ((MkQubit newcounter :: v))

||| Used for tests in Main.
private
mkQubitV : (from:Nat) -> (i:Nat) -> Vect i Qubit
mkQubitV Z Z = []
mkQubitV (S k) Z = []
mkQubitV Z (S k) = (MkQubit Z :: mkQubitV (S Z) k)     
mkQubitV (S n) (S k) = (MkQubit (S n) :: mkQubitV (S (S n)) k)  


||| Used for tests in Main.
private
mkQubitList : (from:Nat) -> (i:Nat) -> LVect i Qubit
mkQubitList Z Z = []
mkQubitList (S k) Z = []
mkQubitList Z (S k) = (MkQubit Z :: mkQubitList (S Z) k)     
mkQubitList (S n) (S k) = (MkQubit (S n) :: mkQubitList (S (S n)) k)  

----- IMPLEMENTATION OF QUANTUMSTATE: LINEAR-ALGEBRAIC SIMULATION -----------
public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> Unitary n -> Vect n Qubit -> Nat -> SimulatedOp n

{-
applyUnitary_ : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary_ v u us = 
    let (us1 # v') # ind = listIndices us v 
        us2 = applyCirc ind u us1
    in pure1 (us2 # v') where
      applyCirc : Vect i Nat -> Unitary i -> (1 _ : SimulatedOp n) -> SimulatedOp n
      applyCirc v IdGate ust = ust
      applyCirc v gate (MkSimulatedOp vs un counter) = 
      --let MkUnitaryUse vs un counter = applyCirc v g st in
      MkSimulatedOp vs (UnitaryLinear.apply gate un v {prf = believe_me ()}) counter 
-}

export
listIndex : (1 _ : SimulatedOp n) -> (1 _ : Qubit) -> LFstPair (LPair (SimulatedOp n) Qubit) Nat
listIndex (MkSimulatedOp qs us v counter) q = let (q, k) = qubitToNatPair q in
        (MkSimulatedOp qs us v counter # q) # (listIndex' v q)


lvectify : (1 _ : Vect i Qubit) -> (LVect i Qubit)
lvectify [] = []
lvectify (x :: xs) = LinearTypes.(::) x (lvectify xs)

mergeVects : (1 _ : Vect n Qubit) -> (1 _ : Vect i Qubit) -> ( LVect i Qubit)
mergeVects [] [] = []
mergeVects [] vect = lvectify vect
mergeVects (x :: xs) [] = mergeVects xs []
mergeVects (x :: xs) (y :: ys) = mergeVects xs (y::ys)

mergeLVects : (1 _ : LVect n Qubit) -> (1 _ : LVect i Qubit) -> (LVect i Qubit)
mergeLVects [] [] = []
mergeLVects [] lvect = lvect
mergeLVects (xs) [] = mergeVects (toVectQ xs) []
mergeLVects (xs) (ys) = mergeVects (toVectQ xs) (toVectQ ys)

||| Applying a circuit to some qubits
{-private
applyUnitary' : {n : Nat} -> {i : Nat} ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' ust (MkSimulatedOp qs un v counter) = let (Builtin.(#) opOut lvect) = (UnitaryOp.run' (MkSimulatedOp qs un v counter) ust) in do
  pure1 (Builtin.(#) opOut lvect)
-}
applyCirc : {n:Nat} -> Vect n Nat -> Unitary n -> (1 _ : SimulatedOp n) -> SimulatedOp n
applyCirc v IdGate qst = qst
applyCirc {n = n} v (H j g) st = 
  let k = indexLT j v 
      h = simpleTensor matrixH n k
      MkSimulatedOp qst urest q counter = applyCirc v g st
  in MkSimulatedOp (h `matrixMult` qst) IdGate q counter
applyCirc {n = n}  v (P p j g) st = 
  let k = indexLT j v
      ph = simpleTensor (matrixP p) n k
      MkSimulatedOp qst urest q counter = applyCirc v g st
  in MkSimulatedOp (ph `matrixMult` qst) IdGate q counter
applyCirc {n = n} v (CNOT c t g) st = 
  let kc = indexLT c v
      kt = indexLT t v
      cn =  tensorCNOT n kc kt
      MkSimulatedOp qst urest q counter = applyCirc v g st
  in MkSimulatedOp (cn `matrixMult` qst) IdGate q counter

applyUnitary' : {n : Nat} -> {i : Nat} -> ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' ust (MkSimulatedOp qs un v counter) = 
  let (MkSimulatedOp qsOut unOut vOut counterOut) # lvect = (runUStateT (MkSimulatedOp qs un v counter) ust) in
  let --(qs # v') # ind = listIndices opOut lvect 
      qs2 = applyCirc (toVectN v) unOut (MkSimulatedOp qsOut unOut vOut counterOut)
  in pure1 (Builtin.(#) qs2  lvect)

    
||| Apply a unitary circuit to a SimulatedOp Alt
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated ust = MkQST (applyUnitary' ust)

applyUDirectlySimulated' : {n : Nat} -> {i : Nat} -> Unitary i -> (1_ : LVect i Qubit) -> (1_ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUDirectlySimulated' ui li (MkSimulatedOp qs un v counter) = 
                      let lvOut # vect = distributeDupedLVectVect li in
                          let unew # _ = applyOrErrorIO ui IdGate vect in
                              let qs2 = applyCirc (toVectN v) unew (MkSimulatedOp qs un v counter) in
                                  pure1 (qs2 # lvOut)


applyUDirectlySimulated : {n : Nat} -> {i : Nat} -> Unitary i -> (1_ : LVect i Qubit) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUDirectlySimulated ui li  = MkQST (applyUDirectlySimulated' ui li)

||| Auxiliary function for applying a circuit to some qubits
private
applyUnitaryAbs' : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitaryAbs' lvectIn ust (MkSimulatedOp qs un v counter) = let (Builtin.(#) opOut lvect) = (runUStateT (MkSimulatedOp qs un v counter) ust) in do
  pure1 (Builtin.(#) opOut (mergeLVects lvect lvectIn))

||| Apply a unitary circuit to a SimulatedOp
export
applyUnitarySimulatedAbs : {n : Nat} -> {i : Nat} -> (1_ : LVect i Qubit) ->
  ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulatedAbs lvect q = MkQST (applyUnitaryAbs' lvect q)


||| Auxiliary function for measurements
private
measure' : {n : Nat} -> (i : Nat) ->
           (1 _ : SimulatedOp (S n)) ->
           R (LFstPair (SimulatedOp n) Bool)
measure' {n} i (MkSimulatedOp v un w counter) = do
  let projector0 = simpleTensor matrixKet0Bra0 (S n) i
  let projection0 = projector0 `matrixMult` v
  let norm20 = normState2 projection0
  let projector1 = simpleTensor matrixKet1Bra1 (S n) i
  let projection1 = projector1 `matrixMult` v
  let norm21 = normState2 projection1
  let newQubits = removeElem w i
  randnb <- liftIO1 randomIO
  if randnb < norm20
     then do
       let proj = multScalarMatrix (inv (sqrt norm20) :+ 0) projection0
       pure1 (MkSimulatedOp (projectState {n} proj i False) IdGate newQubits counter # False)
     else do
       let proj = multScalarMatrix (inv (sqrt norm21) :+ 0) projection1
       pure1 (MkSimulatedOp (projectState {n} proj i True) IdGate newQubits counter # True)

||| Helper, so that we only have to recalculate the counter once
private
measureQubits'' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedOp (i + n)) -> R (LPair (SimulatedOp n) (Vect i Bool))
measureQubits'' [] qs = pure1 (qs # [])
measureQubits'' (x :: xs) qs = 
  let (qs' # q) # y = listIndex qs x in
    let (q, k) = qubitToNatPair q in 
      do
      (s # b) <- measure' y qs'
      (s1 # bs) <- measureQubits'' xs s
      case bs of 
          [] => pure1 (s1 # [b])
          (b' :: bs') => pure1 (s1 # (b :: b' :: bs'))

||| Auxiliary function for measurements
private
measureQubits' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedOp (i + n)) -> R (LPair (SimulatedOp n) (Vect i Bool))
measureQubits' [] qs = pure1 (qs # [])
measureQubits' (x :: xs) qs = 
  let (qs' # q) # y = listIndex qs x in
    let (q, k) = qubitToNatPair q in 
      do
      (s # b)<- measure' y qs'
      (MkSimulatedOp stfin unfin vfin counter # bs) <- measureQubits'' xs s
      case bs of 
          [] => pure1 (MkSimulatedOp stfin unfin vfin (reCalculateCounter vfin) # [b])
          (b' :: bs') => pure1 (MkSimulatedOp stfin unfin vfin (reCalculateCounter vfin) # (b :: b' :: bs'))

------- SIMULATE CIRCUITS : OPERATIONS ON QUANTUM STATES ------

||| Add new qubits to a Quantum State
export
newQubitsSimulated : (p : Nat) -> QStateT (SimulatedOp n) (SimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulated p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : SimulatedOp m) -> R (LPair (SimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkSimulatedOp qs un v counter) =
    let s' = toTensorBasis (ket0 q)
        (qubits # (v', newcounter))= newQubitsPointers q counter v
    in pure1 (MkSimulatedOp (tensorProductVect qs s') ( un # IdGate )  (v ++ v') (newcounter) # qubits)


||| Measure some qubits in a quantum state
export
measureSimulated : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (SimulatedOp (i + n)) (SimulatedOp n) (Vect i Bool)
measureSimulated v = MkQST (measureQubits' v)


%hint
export
qubitlvect : (1_ : Qubit) -> LVect 1 Qubit
qubitlvect q = [q]


||| Run all simulations : start with 0 qubit and measure all qubits at the end (end with 0 qubit)
export
runSimulated : {n:Nat} -> QStateT (SimulatedOp 0) (SimulatedOp 0) (Vect n Bool) -> IO (Vect n Bool)
runSimulated s = LIO.run (do
  ((MkSimulatedOp st un w c) # v) <- runQStateT (MkSimulatedOp [[1]] IdGate [] 0) s
  case v of 
       [] => pure []
       (x :: xs) => pure (x :: xs))
 

export
QuantumOp SimulatedOp where
  newQubits    = newQubitsSimulated
  applyUST = applyUnitarySimulated
  applyUnitaryDirectly = applyUDirectlySimulated
  measure      = measureSimulated
  runQ          = runSimulated

--------------------------- BinarySimulatedOp with functions that only QuantumOp has access to-------------------

||| The counter (Nat) here is a count for how many functions we have! We recalculate qubit counters anyway.
public export
data BinarySimulatedOp : Nat -> Type where
  MkBinarySimulatedOp : {n : Nat} -> Unitary n -> Vect n Qubit -> Nat -> String -> BinarySimulatedOp n

||| Reset string
export 
resetNStr: {n:Nat} -> Vect n Nat -> String
resetNStr []  =    ""
resetNStr (x::xs) = "\tcircuit.reset("++ show x ++")\n" ++ resetNStr xs


||| Add the string for resetting qubits  
export
addQubitsResetStr: {n : Nat} -> String -> (counter:Nat) -> Vect n Nat -> String
addQubitsResetStr str counter v =
    let sOut = str ++ "\ndef Function"++ show counter++"(circuit):  \n" 
             ++ resetNStr v ++  
             "\treturn circuit\n\n" in
              sOut

||| New qubits in BinarySimulatedOp
export
newQubitsSimulatedCirc : (p : Nat) -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulatedCirc p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : BinarySimulatedOp m) -> R (LPair (BinarySimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkBinarySimulatedOp un v counter str) =
    let (qubits # (v'))= newQubitsPointersNoCount q  v in 
      let strOut = addQubitsResetStr str counter (toVectN v') in
        pure1 (MkBinarySimulatedOp ( un # IdGate ) (v ++ v') (S counter) (strOut) # qubits)


---------------------------------------------------------

idUp :  {m:Nat} -> (1 _ : Unitary m) -> (q : Nat) -> Unitary (m + q)
idUp um Z = rewrite plusZeroRightNeutral m in um
idUp um (S k) = um # (IdGate {n = (S k)})

idUpNoPrf :  {m:Nat} -> (1 _ : UnitaryNoPrf m) -> (q : Nat) -> UnitaryNoPrf (m + q)
idUpNoPrf um Z = rewrite plusZeroRightNeutral m in um
idUpNoPrf um (S k) = um # (IdGate {n = (S k)})

export
newQubitsUST : {n:Nat} -> (p : Nat) -> UStateT (Unitary n) (Unitary (n+p)) (LVect p Qubit)
newQubitsUST p = MkUST (newQubits' p) where
  newQubits' : {m:Nat} -> (q : Nat) -> (1 _ : Unitary m) ->(LPair (Unitary (m + q)) (LVect q Qubit))
  newQubits' {m} q un = 
    let (qubits # v') = newQubitsPointersNoCount q (mkQubitV 0 m)
    in (idUp un q # qubits)

export
newQubitsUSTNoPrf : {n:Nat} -> (p : Nat) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf (n+p)) (LVect p Qubit)
newQubitsUSTNoPrf p = MkUST (newQubits' p) where
  newQubits' : {m:Nat} -> (q : Nat) -> (1 _ : UnitaryNoPrf m) ->(LPair (UnitaryNoPrf (m + q)) (LVect q Qubit))
  newQubits' {m} q un = 
    let (qubits # v') = newQubitsPointersNoCount q (mkQubitV 0 m)
    in (idUpNoPrf un q # qubits)

public export
interface RunUnitaryOp (0 t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  supplyQubits : {n:Nat} -> (p : Nat) -> UStateT (t n) (t (n+p)) (LVect p Qubit)
  supplyQubits Z     = rewrite plusZeroRightNeutral n in pure []
  supplyQubits (S k) = rewrite lemmaPlusSRight n k in do
    q <- supplyQubit
    qs <- supplyQubits k
    pure (q :: qs)

  ||| Prepare a single new qubit in state |0>
  supplyQubit : {n:Nat} -> UStateT (t n) (t (S n)) Qubit
  supplyQubit = rewrite sym $ lemmaplusOneRight n in do
    [q] <- supplyQubits 1
    pure q
  
  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUStateT : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LVect i Qubit)) -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUStateTSplit : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))) -> UStateT (t n) (t n) (LVect (i+j) Qubit)
     
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  runUnitaryOp : {n:Nat} -> UStateT (t 0) (t n) (LVect n Qubit) -> (t n)



-------------Unitary implementation of UnitaryRun --------------

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTR': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect i Qubit)
applyUSTR' ust un = 
  let (uOut # lvect) = runUStateT IdGate ust in
        let unew = UnitaryLinear.compose uOut un in
          do unew # (lvect)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedR : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> UStateT (Unitary n) (Unitary n) (LVect i  Qubit)
applyUSTSimulatedR ust = MkUST (applyUSTR' ust )

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSplit': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect (i + j) Qubit)
applyUSTSplit' ust un = 
  let (uOut # (lvi # lvj)) = runUStateT IdGate ust in
        let unew = UnitaryLinear.compose uOut un in
          do unew # (lvi ++ lvj)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedSplit : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (Unitary n) (Unitary n) (LVect (i + j) Qubit)
applyUSTSimulatedSplit ust = MkUST (applyUSTSplit' ust )


runUnitaryOp' : {n:Nat} -> UStateT (Unitary 0) (Unitary n) (LVect n Qubit) -> (Unitary n)
runUnitaryOp' ust = let un # lv = runUStateT IdGate ust in
                      let () = discardq lv in
                        un


public export
RunUnitaryOp Unitary where
  supplyQubits = newQubitsUST
  applyUStateT = applyUSTSimulatedR
  runUnitaryOp = runUnitaryOp'
  applyUStateTSplit = applyUSTSimulatedSplit


-------------UnitaryNoPrf implementation of UnitaryRun --------------

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTRNoPrf': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
applyUSTRNoPrf' {n} ust un = 
  let (uOut # lvect) = runUStateT (UnitaryNoPrf.IdGate {n = n}) ust in
        let unew = UnitaryNoPrf.compose uOut un in
          unew # (lvect)

||| UnitaryNoPrfimplementation of abstract UnitaryNoPrfapplication (that is, whatever one built using UStateT)
applyUSTSimulatedRNoPrf : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i  Qubit)
applyUSTSimulatedRNoPrf ust = MkUST (applyUSTRNoPrf' ust )

||| Helper for UnitaryNoPrfimplementation of abstract UnitaryNoPrfapplication (that is, whatever one built using UStateT)
applyUSTSplitNoPrf': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyUSTSplitNoPrf' ust un = 
  let (uOut # (lvi # lvj)) = runUStateT UnitaryNoPrf.IdGate ust in
        let unew = UnitaryNoPrf.compose uOut un in
          unew # (lvi ++ lvj)

||| UnitaryNoPrfimplementation of abstract UnitaryNoPrfapplication (that is, whatever one built using UStateT)
applyUSTSimulatedSplitNoPrf : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyUSTSimulatedSplitNoPrf ust = MkUST (applyUSTSplitNoPrf' ust )


runUnitaryOpNoPrf' : {n:Nat} -> UStateT (UnitaryNoPrf 0) (UnitaryNoPrf n) (LVect n Qubit) -> (UnitaryNoPrf n)
runUnitaryOpNoPrf' ust = let un # lv = runUStateT IdGate ust in
                      let () = discardq lv in
                        un


public export
RunUnitaryOp UnitaryNoPrf where
  supplyQubits = newQubitsUSTNoPrf
  applyUStateT = applyUSTSimulatedRNoPrf
  runUnitaryOp = runUnitaryOpNoPrf'
  applyUStateTSplit = applyUSTSimulatedSplitNoPrf


-------------Other Utilities--------------
export
reCalculateNew : {n:Nat} -> (v: Vect n Nat) -> Nat
reCalculateNew [] = 0
reCalculateNew {n = S k} (x::xs) = smallestMissing (sort ((x::xs)))

export
newVectOrder : {i:Nat} -> (p : Nat) -> (v: Vect i Nat) -> (Vect p Nat)
newVectOrder 0 _ = (([]))
newVectOrder {i} (S p) xs = let newcounter = (reCalculateNew (xs)) in
                let (v) = newVectOrder p (newcounter :: xs)
                  in ((newcounter :: v))

export
plusminusisN : (i,n:Nat) -> Vect (plus i (minus n i)) Nat -> Vect (plus (minus n i) i) Nat
plusminusisN i n vect = rewrite sym $ plusCommutative i (minus n i) in vect
 
export
plusminusn : (i,n:Nat) -> LTE i n -> Vect (plus (minus n i) i) Nat -> Vect n Nat
plusminusn i n lte vect = rewrite sym $ plusMinusLte i n lte in vect

export
newVectOrderN : {i:Nat} -> (n:Nat) -> (v: Vect i Nat) -> (Vect n Nat)
newVectOrderN n [] = newVectOrder n []
newVectOrderN {i} n v = case isLTE i n of
    Yes prfYes => let vect = (v ++ newVectOrder (minus n i) v) in 
                    let vectOut = (plusminusn i n prfYes (rewrite plusCommutative (minus n i) i in vect))
                      in vectOut
    No prf => toVectN $ makeNeutralVect n -- irrelevant in terms of control flow

export
findInLin : {n:Nat} -> (q : Nat) -> Vect (S n) Nat -> (Vect n Nat)
findInLin ( q) [] impossible
findInLin {n = Z} ( q) ( m :: xs) = []
findInLin {n = S r} ( q) ( m :: xs) = case decEq q m of
  Yes _ => xs
  No _ => ( m :: (findInLin {n = r} ( q) xs))
findInLin ( a) (x :: xs) = xs 

{- UNUSED but could be used:


export
makeSafeForAbstractControl : UnitaryOp t => {n:Nat} -> (1c:Qubit) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (Qubit) (LVect i Qubit))
makeSafeForAbstractControl any [] = pure $ any # []
makeSafeForAbstractControl (MkQubit Z) [MkQubit Z] = pure $ (MkQubit Z) # [MkQubit Z] --invalid case in our context, no change
makeSafeForAbstractControl (MkQubit Z) [MkQubit (S m)] = pure $ (MkQubit Z) # [MkQubit m]
makeSafeForAbstractControl (MkQubit (S m)) [MkQubit Z] = pure $ (MkQubit (S m)) # [MkQubit Z]
makeSafeForAbstractControl (MkQubit Z) (MkQubit Z :: qs) = pure $ (MkQubit Z) # (MkQubit Z :: qs) --invalid case in our context, so whatever is fine
makeSafeForAbstractControl (MkQubit Z) (MkQubit (S m) :: qs) = do
  control # rest <- makeSafeForAbstractControl (MkQubit Z) qs
  pure $ control # (MkQubit m :: rest)
makeSafeForAbstractControl (MkQubit (S k)) (MkQubit (S m) :: qs) = case isLT k m of
  Yes prfYes => do 
    control # rest <- makeSafeForAbstractControl (MkQubit (S k)) qs
    pure $ control # (MkQubit m :: rest)
  No prfNo => do 
    control # rest <- makeSafeForAbstractControl (MkQubit (S k)) qs
    pure $ control # (MkQubit (S m ):: rest)
makeSafeForAbstractControl (MkQubit (S k)) (MkQubit Z :: qs) = do 
    control # rest <- makeSafeForAbstractControl (MkQubit (S k)) qs
    pure $ control # (MkQubit (Z) :: rest)
    -}