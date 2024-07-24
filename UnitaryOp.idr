module UnitaryOp

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


||| The UnitaryOpBad interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Qubits it contains.
export
interface UnitaryOp (0 t : Nat -> Type) where
{-}
  applyUnitaryAbs : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n+i)) (t (n+i)) (LVect i Qubit)

  applyHAbs : {n : Nat} -> (1 _ :  LVect 1 Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)

  applyPAbs : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)

  applyCNOTAbs : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)

  applyControlledP : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)

  applytU : {n : Nat} -> {i : Nat} ->  (1 _ : LVect i Qubit) -> t i -> UStateT (t (n+i)) (t (n+i)) (LVect i Qubit)
-}
  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LVect i Qubit)

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


  ||| sequence to the end
  run :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit) ) -> (LPair (t n) (LVect i Qubit))


export
single : LVect 1 Qubit -> Qubit
single [q] = q

public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> Vect n Qubit -> Nat -> SimulatedOp n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------


||| Find an element in a list : used to find the wire of a qubit
public export
listIndex' : {n : Nat} -> Vect n Qubit -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

public export
listIndex : (1 _ : SimulatedOp n) -> (1 _ : Qubit) -> LFstPair (LPair (SimulatedOp n) Qubit) Nat
listIndex (MkSimulatedOp qs v counter) (MkQubit k) = (MkSimulatedOp qs v counter # MkQubit k) # (listIndex' v (MkQubit k))

public export
listIndices : (1 _ : SimulatedOp n) -> (1 _ : LVect i Qubit) -> LFstPair (LPair (SimulatedOp n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y :: ys)

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
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' v u q = 
  let (qs # v') # ind = listIndices q v 
      qs2 = applyCirc ind u qs
  in (qs2 # v') where
    applyCirc : Vect i Nat -> Unitary i -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v IdGate qst = qst
    applyCirc v (H j g) st = 
      let k = indexLT j v 
          h = simpleTensor matrixH n k
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let k = indexLT j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let kc = indexLT c v
          kt = indexLT t v
          cn =  tensorCNOT n kc kt
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (cn `matrixMult` qst) q counter

applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect ui)

public export
run' : {i:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> LPair (SimulatedOp n) (LVect i Qubit)
run' {i = i} simop ust = runUStateT simop ust      



{-}
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
export
UnitaryOp SimulatedOp where
  applyUnitary = applyUnitarySimulated
  run          = run' 