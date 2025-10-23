module UnitaryOpNoLVec

import Data.Vect
import Data.Nat
import Control.Monad.State
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Lemmas
import UnitaryLinear
import UStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Data.Maybe
import QStateT
import Data.Linear.Notation
import Data.Linear.Interface
import Qubit



 
||| The UnitaryOpBad interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Qubits it contains.
export
interface UnitaryOpNoLVec (0 t : Nat -> Type) where

  applyUnitaryAbs : {i : Nat} -> (1_ : UStateT (t i) (t i) (LVect i Qubit))
                    -> UStateT (t i) (t i) (LVect i Qubit)

  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitary : {i : Nat} -> Unitary i -> UStateT (t i) (t i) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single Qubit
  applyH : UStateT (t 1) (t 1) (LVect 1 Qubit)
  applyH = do
    [q1] <- applyUnitary {i = 1} HGate 
    pure [q1]

  ||| Apply a P gate to a single Qubit
  applyP : Double ->  UStateT (t 1) (t 1) (LVect 1 Qubit)
  applyP p = do
    [q1] <- applyUnitary {i = 1} (PGate p)
    pure [q1]

  ||| Apply the CNOT gate to a pair of Qubits
  applyCNOT : UStateT (t 2) (t 2) (LVect 2 Qubit)
  applyCNOT = do
    [q1,q2] <- applyUnitary {i = 2} CNOTGate
    pure (q1::q2::[])
  
  applyControlledU : {i:Nat} -> (1 _ : Qubit) -> (1_ : UStateT (t i) (t i) (LVect i Qubit))
                               -> UStateT (t i) (t i) (LVect (S i) Qubit) 
  ||| sequence to the end
  run :  {i : Nat} -> (1_: (t i)) -> (1_ : UStateT (t i) (t i) (LVect i Qubit) ) -> (LPair (t i) (LVect i Qubit))

%hint
export
singleQubit : (1 _ : LVect 1 Qubit)-> Qubit
singleQubit [q] = q

public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {i : Nat} -> Matrix (power 2 i) 1 -> Vect i Qubit -> Nat -> SimulatedOp i

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------
  
   
   
  
||| Find an element in a list : used to find the wire of a qubit

vQtovN : {i:Nat} -> (Vect i Qubit) -> (Vect i Nat)
vQtovN [] = []
vQtovN (MkQubit k :: xs) = k :: vQtovN xs

public export
listIndices : (1 _ : SimulatedOp i) -> LFstPair (SimulatedOp i) (Vect i Nat)
listIndices (MkSimulatedOp qs v counter) = ((MkSimulatedOp qs v counter) # (vQtovN v))


||| Remove an element at a given index in the vector
public export
removeElem : {n : Nat} -> Vect (S n) Qubit -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k


||| add the indices of the new qubits to the vector in the SimulatedOp
public export
newQubitsPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointers 0 _ = ([] # [])
newQubitsPointers (S p) counter = 
  let (q # v) = newQubitsPointers p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)

||| Auxiliary function for applying a circuit to some qubits
private
applyUnitary' : {i : Nat} -> Unitary i -> (1 _ : SimulatedOp i) -> (LPair (SimulatedOp i) (LVect i Qubit))
applyUnitary' u q = 
  let qs # ind = listIndices q 
      qs2 = applyCirc ind u qs
  in (qs2 # (toLVectQ ind)) where
    applyCirc : Vect i Nat -> Unitary i -> (1 _ : SimulatedOp i) -> SimulatedOp i
    applyCirc v IdGate qst = qst
    applyCirc v (H j g) st = 
      let k = indexLT j v 
          h = simpleTensor matrixH i k
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let k = indexLT j v
          ph = simpleTensor (matrixP p) i k
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let kc = indexLT c v
          kt = indexLT t v
          cn =  tensorCNOT i kc kt
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (cn `matrixMult` qst) q counter

applyUnitarySimulated : {i : Nat} -> Unitary i -> UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit)
applyUnitarySimulated ui = MkUST (applyUnitary' ui)

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


public export
run' : {i:Nat} -> (1_: SimulatedOp i) -> (1 _ : UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit) ) -> LPair (SimulatedOp i) (LVect i Qubit)
run' {i = i} simop ust = runUStateT simop ust
   
||| Auxiliary function for applying a circuit to some qubits
private
applyUnitaryAbs' : {i : Nat} ->
  (1_ : UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit)) -> (1 _ : SimulatedOp i) -> (LPair (SimulatedOp i) (LVect i Qubit))
applyUnitaryAbs' ust (MkSimulatedOp qs v counter) = let (Builtin.(#) opOut lvect) = (UnitaryOpNoLVec.run' (MkSimulatedOp qs v counter) ust) in do
 (Builtin.(#) opOut lvect)

export
applyUnitaryAbsSimulated : {i : Nat} ->
  (1_ : (UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit) ))-> UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit)
applyUnitaryAbsSimulated q = MkUST (applyUnitaryAbs' q)

private
applyControlledAbs' : {i : Nat} -> (1 _ : Qubit) ->
  (1_ : UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit)) -> (1 _ : SimulatedOp i) -> (LPair (SimulatedOp i) (LVect (S i) Qubit))
applyControlledAbs' q ust (MkSimulatedOp qs v counter) = let (Builtin.(#) opOut lvect) = (UnitaryOpNoLVec.run' (MkSimulatedOp qs v counter) ust) in do
 (Builtin.(#) opOut (q ::lvect ))

 
export
applyControlledAbsSimulated : {i : Nat} -> (1_ : Qubit) ->
  (1_ : (UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit) )) -> UStateT (SimulatedOp i) (SimulatedOp i) (LVect (S i) Qubit)
applyControlledAbsSimulated control q = MkUST (applyControlledAbs' control q)

export
UnitaryOpNoLVec SimulatedOp where
  applyUnitary = applyUnitarySimulated
  applyUnitaryAbs  = applyUnitaryAbsSimulated
  applyControlledU = applyControlledAbsSimulated
  run          = run' 

{-
public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> (1_: Vect n Qubit) -> Nat -> SimulatedOp n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------

||| Find an element in a list : used to find the wire of a qubit
export
listIndex' : {n : Nat} -> (1_: Vect n Qubit) -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

export
listIndex : (1 _ : SimulatedOp n) -> (1 _ : Qubit) -> LPair (LPair (SimulatedOp n) Qubit) Nat
listIndex (MkSimulatedOp qs v counter) (MkQubit k) = let MkPair v' v'' = toVectQNonLin v in 
                  (MkSimulatedOp qs v' counter # MkQubit k) # (listIndex' v'' (MkQubit k))

reLinNat : (1_: Nat) -> Qubit
reLinNat Z = MkQubit Z
reLinNat (S k) = MkQubit (S k)       

lCons : (1_: Nat) -> (1_: Vect k Nat) -> Vect (S k) Nat
lCons Z [] = [Z]
lCons Z (x :: xs) = Z :: x :: xs
lCons (S k) [] = [(S k)]
lCons (S k) (x :: xs) = (S k) :: x :: xs  


export
listIndices : (1 _ : SimulatedOp n) -> (1 _ : LVect i Qubit) -> LPair (LPair (SimulatedOp n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y `lCons` ys)

||| Remove an element at a given index in the vector
export
removeElem : {n : Nat} -> (1_: Vect (S n) Qubit) -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k


||| add the indices of the new qubits to the vector in the SimulatedOp
export
newQubitsPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointers 0 _ = ([] # [])
newQubitsPointers (S p) counter = 
  let (q # v) = newQubitsPointers p (S counter)
  in (MkQubit counter :: q) # (MkQubit counter :: v)


newQubits : (p : Nat) -> (counter : Nat) -> (Vect p Qubit)
newQubits 0 _= []
newQubits (S p) counter = (MkQubit counter :: (newQubits p (S counter)))

nothingToNil : (1_: ()) -> Pair (Vect 0 Qubit) ()
nothingToNil () = MkPair [] ()

nilPlus : (1_: (Vect 0 Qubit)) -> (1_: Vect i Qubit) -> LPair (Vect i Qubit) (Vect 0 Qubit)
nilPlus [] xs = (#) xs []


interface Collapsable (p : Type -> Type -> Type) where
  collapse : p a () -@ a


Collapsable LPair where
  collapse ((#) a ()) = a

public export
vectConsumed : (1_: Vect i elem) -> (1_: ()) -> (Vect i elem)
vectConsumed vect empty = collapse ((#) vect empty)

public export
Consumable (Vect i elem) where 
  consume [] = ()
  consume (x :: xs) = ()

private
applyUnitary' : {n : Nat} -> {i : Nat} -> 
   (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' v u q = 
  let (qs # v') # ind = listIndices q v
      qs2 = applyCirc ind u qs
  in (qs2 # v') where
    applyCirc : (1_: Vect i Nat) -> Unitary i -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v IdGate (MkSimulatedOp qst q counter) = (MkSimulatedOp qst (vectConsumed q (consume v)) counter)
    applyCirc v (H j g) st = 
      let vs # k = indexLTL j v 
          h = simpleTensor matrixH n k
          MkSimulatedOp qst q counter = applyCirc vs g st
      in MkSimulatedOp (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let vs # k = indexLTL j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedOp qst q counter = applyCirc vs g st
      in MkSimulatedOp (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let vcs # kc= indexLTL c v
          vts # kt= indexLTL t vcs
          cn =  tensorCNOT n kc kt
          MkSimulatedOp qst q counter = applyCirc vts g st
      in MkSimulatedOp (cn `matrixMult` qst) q counter

applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect ui)

run' : {i:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> LPair (SimulatedOp n) (LVect i Qubit)
run' {i = i} simop ust = runUStateT simop ust 
-}
