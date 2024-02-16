module CombinedOp

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


||| The UnitaryOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Qubits it contains.
export
interface CombinedOp (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single Qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> UStateT (t n) (t n) Qubit
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure q1

  ||| Apply a P gate to a single Qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) Qubit
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure q1

  ||| Apply the CNOT gate to a pair of Qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair Qubit Qubit)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1 # q2)

  ||| sequence to the end
  run : (1 _ : UStateT (t m) (t m) (LVect n Qubit) ) -> ((LPair (Unitary n) (LVect n Qubit))) 

