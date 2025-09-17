module QuantumOp

import Data.Vect
import Data.Vect.Sort
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
import UnitaryOp
import UStateT
import Control.Linear.LIO
import Qubit

||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.

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
  applyUnitaryQ : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LVect i Qubit)) -> QStateT (t n) (t n) (LVect i Qubit)

  ||| Apply Hadamard to specified qubit
  applyHQ: UnitaryOp t => {n : Nat} -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 1 Qubit)
  applyHQ q = do
              q <- applyUnitaryQ {t = t} (applyH {t = t} {n = n } (q))
              pure q

  ||| Measure some qubits in a quantum state
  public export
  measureQ : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (t (i + n)) (t n) (Vect i Bool)
  
  ||| Measure only one qubit
  measureQubit : {n : Nat} -> (1 _ : Qubit) -> QStateT (t (S n)) (t n) Bool
  measureQubit q = do
    [b] <- measureQ [q]
    pure b
  ||| Same as measure, but with an initial state of n + i instead of i + n qubits to help with theorem proving in some cases
  -- public export
  -- measure2 : {n : Nat} -> {i : Nat} -> (LVect i Qubit) -> QStateT (t (n + i)) (t n) (Vect i Bool)
  -- measure2 v = rewrite plusCommutative n i in measure v

  ||| Measure all qubits in a quantum state
  ||| Because of a bug in Idris2, we use the implementation below.
  ||| However, the implementation commented out is preferable if the bug gets fixed.
  public export
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

----- IMPLEMENTATION OF QUANTUMSTATE: LINEAR-ALGEBRAIC SIMULATION -----------

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
applyUnitary' : {n : Nat} -> {i : Nat} -> ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' ust (MkSimulatedOp qs un v counter) = 
  let (opOut # lvect) = (UnitaryOp.run' (MkSimulatedOp qs un v counter) ust) in
  let --(qs # v') # ind = listIndices opOut lvect 
      qs2 = applyCirc (toVectN v) un opOut
  in pure1 (Builtin.(#) qs2  lvect) where
    applyCirc : Vect n Nat -> Unitary n -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v IdGate qst = qst
    applyCirc v (H j g) st = 
      let k = indexLT j v 
          h = simpleTensor matrixH n k
          MkSimulatedOp qst urest q counter = applyCirc v g st
      in MkSimulatedOp (h `matrixMult` qst) IdGate q counter
    applyCirc v (P p j g) st = 
      let k = indexLT j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedOp qst urest q counter = applyCirc v g st
      in MkSimulatedOp (ph `matrixMult` qst) IdGate q counter
    applyCirc v (CNOT c t g) st = 
      let kc = indexLT c v
          kt = indexLT t v
          cn =  tensorCNOT n kc kt
          MkSimulatedOp qst urest q counter = applyCirc v g st
      in MkSimulatedOp (cn `matrixMult` qst) IdGate q counter
    
||| Apply a unitary circuit to a SimulatedOp Alt
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated ust = MkQST (applyUnitary' ust)


||| Auxiliary function for applying a circuit to some qubits
private
applyUnitaryAbs' : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitaryAbs' lvectIn ust (MkSimulatedOp qs un v counter) = let (Builtin.(#) opOut lvect) = (UnitaryOp.run' (MkSimulatedOp qs un v counter) ust) in do
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

||| Auxiliary function for measurements
private
measureQubits' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedOp (i + n)) -> R (LPair (SimulatedOp n) (Vect i Bool))
measureQubits' [] qs = pure1 (qs # [])
measureQubits' (x :: xs) qs = do
  let (qs' # (MkQubit k)) # y = listIndex qs x
  (s # b) <- measure' y qs'
  (s1 # bs) <- measureQubits' xs s
  case bs of 
       [] => pure1 (s1 # [b])
       (b' :: bs') => pure1 (s1 # (b :: b' :: bs'))

------- SIMULATE CIRCUITS : OPERATIONS ON QUANTUM STATES ------

smallestMissing: (v: Vect n Nat) -> Nat
smallestMissing [] = Z
smallestMissing [Z] = S Z 
smallestMissing [S k] = S (S k)
smallestMissing (x::y::ys) = case decEq (S x) y of
  Yes _ => smallestMissing (y::ys)
  No _ => (S x)

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

private 
newQubitsPointersOld : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersOld 0 _ = ([] # [])
newQubitsPointersOld (S p) counter = 
  let (q # v) = newQubitsPointersOld p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)  

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

{-

applyUnitary' : {n : Nat} -> {i : Nat} ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' ust simopIn = let (Builtin.(#) simopOut lvectOut) = (UnitaryOp.run simopIn ust) in do
    pure1 (Builtin.(#) simopOut lvectOut)  



pentupleNat : (1_ : Nat) -> Vect 5 Nat
pentupleNat Z = [Z,Z,Z,Z,Z]
pentupleNat (S k) = (S k) :: (S k) :: (S k) :: (S k) :: [(S k)]
||| Auxiliary function for measurements
private
measure' : {n : Nat} -> (1_ : Nat) ->
           (1 _ : SimulatedOp (S n)) ->
           R (LFstPair (SimulatedOp n) Bool)
measure' {n} i (MkSimulatedOp v w counter) = do
  let [i1, i2, i3, i4, i5] = pentupleNat i
  let projector0 = simpleTensor matrixKet0Bra0 (S n) i1
  let projection0 = projector0 `matrixMult` v
  let norm20 = normState2 projection0
  let projector1 = simpleTensor matrixKet1Bra1 (S n) i2
  let projection1 = projector1 `matrixMult` v
  let norm21 = normState2 projection1
  let newQubits = removeElem w i3
  randnb <- liftIO1 randomIO
  if randnb < norm20
     then do
       let proj = multScalarMatrix (inv (sqrt norm20) :+ 0) projection0
       pure1 (MkSimulatedOp (projectState {n} proj i4 False) newQubits counter # False)
     else do
       let proj = multScalarMatrix (inv (sqrt norm21) :+ 0) projection1
       pure1 (MkSimulatedOp (projectState {n} proj i5 True) newQubits counter # True)

||| Auxiliary function for measurements
private
measureQubits' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedOp (i + n)) -> R (LPair (SimulatedOp n) (Vect i Bool))
measureQubits' [] qs = pure1 (qs # [])
measureQubits' (x :: xs) qs = do
  let (qs' # (MkQubit k)) # y = listIndex qs x
  (s # b) <- measure' y qs'
  (s1 # bs) <- measureQubits' xs s
  case bs of 
       [] => pure1 (s1 # [b])
       (b' :: bs') => pure1 (s1 # (b :: b' :: bs'))

------- SIMULATE CIRCUITS : OPERATIONS ON QUANTUM STATES ------

pp : (1_: Vect m elem) -> (ys : Vect n elem) -> Vect (m + n) elem
pp []      ys = ys
pp (x::xs) ys = x :: xs `pp` ys

||| Add new qubits to a Quantum State
export
newQubitsSimulated : (p : Nat) -> QStateT (SimulatedOp n) (SimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulated p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : SimulatedOp m) -> R (LPair (SimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkSimulatedOp qs un v counter) =
    let s' = toTensorBasis (ket0 q)
        (qubits # v') = newQubitsPointers q counter
    in pure1 (MkSimulatedOp (tensorProductVect qs s') (v `pp` v') (counter + q) # qubits)


||| Apply a unitary circuit to a SimulatedOp
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
   ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated q = MkQST (applyUnitary' q)

||| Measure some qubits in a quantum state
export
measureSimulated : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (SimulatedOp (i + n)) (SimulatedOp n) (Vect i Bool)
measureSimulated v = MkQST (measureQubits' v)
 
bang : L IO t -@ L1 IO (!* t)
bang io = io >>= \ a => pure1 (MkBang a)
-}
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
  applyUnitaryQ = applyUnitarySimulated
  measureQ      = measureSimulated
  runQ          = runSimulated
{- 

export
QuantumOp Unitary where
  newQubits    = newQubits
  applyUnitary = apply
  measure      = measure
run          = run -}

