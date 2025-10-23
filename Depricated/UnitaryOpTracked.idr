
module UnitaryOpTracked

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
import Qubit


||| The UnitaryOpBad interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Qubits it contains.
export
interface UnitaryOpT (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitaryT : (n:Nat) -> (i:Nat) ->
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LPair (Unitary i) (LVect i Qubit))

  ||| Apply the Hadamard gate to a single Qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair (Unitary 1) Qubit)
  applyH q = do
    u # [q1] <- applyUnitaryT n 1 [q] HGate 
    pure (u # q1)

  ||| Apply a P gate to a single Qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair (Unitary 1) Qubit)
  applyP p q = do
    u # [q1] <- applyUnitaryT n 1 [q] (PGate p)
    pure (u # q1)

  ||| Apply the CNOT gate to a pair of Qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair (Unitary 2) (LPair Qubit Qubit))
  applyCNOT q1 q2 = do
    u # [q1,q2] <- applyUnitaryT n 2 ([q1,q2]) CNOTGate
    pure (u # (q1 # q2))


  ||| sequence to the end
  run : (n : Nat) -> (i:Nat) -> (1 _ : UStateT (t n) (t n) (LPair (Unitary i) (LVect i Qubit)) ) -> ((LPair (Unitary i) (LVect i Qubit))) 

