module UnitaryOp

import Data.Vect
import Data.Nat
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import System.Random
import Lemmas
import UStateT
import Control.Linear.LIO
import LinearTypes
import Unitary

||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.
export
data Qubit : Type where
  MkQubit : (n : Nat) -> (k : Nat) -> {auto prf: LT k n} -> Qubit
  MkQubit n k = justFinLemma 

||| The UnitaryOp interface is used to abstract over the representation of a
||| unitarz operation. It is parameterised by the number of qubits it contains.
export
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  newQubits : (p : Nat) -> UStateT (t n) (t (n+p)) (LVect p Qubit)
  newQubits Z     = rewrite plusZeroRightNeutral n in pure []
  newQubits (S k) = rewrite lemmaPlusSRight n k in do
    q <- newQubit
    qs <- newQubits k
    pure (q :: qs)

  ||| Prepare a single new qubit in state |0>
  newQubit : UStateT (t n) (t (S n)) Qubit
  newQubit = rewrite sym $ lemmaplusOneRight n in do
    [q] <- newQubits 1
    pure q

  ||| Apply a unitary circuit to the qubits specified by the LVect argument
  applyUnitary : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> UStateT (t n) (t n) Qubit
  applyH q = do
    [q1] <- apply {n = n} {}
    pure q1
      {n : Nat} -> {i : Fin n} -> 
      Unitary (finToNat i) -> Unitary n -> 
      (v : Vect (finToNat i) (Fin n)) -> 
      {auto prf : (allDifferentFin v) = True} ->
      {auto valid : LTE 2 n} -> 

  ||| Apply a P gate to a single qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) Qubit
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure q1

  ||| Apply the CNOT gate to a pair of qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair Qubit Qubit)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} [q1,q2] CNOTGate
    pure (q1 # q2)

  ||| Measure some qubits in a quantum state
  public export
  measure : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (i + n)) (t n) (Vect i Bool)
  measure [] = pure []
  measure (q :: qs) = do
    b <- measureQubit q
    bs <- measure qs
    pure (b `consLin` bs)

  ||| Measure only one qubit
  measureQubit : {n : Nat} -> (1 _ : Qubit) -> UStateT (t (S n)) (t n) Bool
  measureQubit q = do
    [b] <- measure [q]
    pure b

  ||| Same as measure, but with an initial state of n + i instead of i + n qubits to help with theorem proving in some cases
  -- public export
  -- measure2 : {n : Nat} -> {i : Nat} -> (LVect i Qubit) -> UStateT (t (n + i)) (t n) (Vect i Bool)
  -- measure2 v = rewrite plusCommutative n i in measure v

  ||| Measure all qubits in a quantum state
  ||| Because of a bug in Idris2, we use the implementation below.
  ||| However, the implementation commented out is preferable if the bug gets fixed.
  public export
  measureAll : {n : Nat} -> (1 _ : LVect n Qubit) -> UStateT (t n) (t 0) (Vect n Bool)
  measureAll []        = pure []
  measureAll (q :: qs) = do
    b <- measureQubit q
    bs <- measureAll qs
    pure (b `consLin` bs)
  --measureAll qs = rewrite sym $ plusZeroRightNeutral n in measure qs
                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  run : UStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)