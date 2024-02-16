module QuantumOpNew

import Data.Vect
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
import Unitary
import CombinedOp
import UStateT
import QFT

private
data Qubits : Type where
  MakeQubits : Nat -> Qubits




||| The QuantumOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of qubits it contains.
export
interface QuantumOpNew (0 t : Nat -> Type) where

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
  
  |||Use the information in the list of qubits we have to create a unitary  
  makeUnitary : {n:Nat} -> {p:Nat} -> (LVect p Qubit) -> (QStateT (t n) (t n) (CombinedOp t)) 

  ||| Apply a unitary circuit to the qubits specified by the LVect argument
  applyUnitary : {n : Nat} -> {i : Nat} -> CombinedOp t -> QStateT (t 0) (t n) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> QStateT (t n) (t n) Qubit

  ||| Apply a P gate to a single qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> QStateT (t n) (t n) Qubit

  ||| Apply the CNOT gate to a pair of qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> QStateT (t n) (t n) (LPair Qubit Qubit)

  ||| Measure some qubits in a quantum state
  public export
  measure : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (t (i + n)) (t n) (Vect i Bool)

  ||| Measure only one qubit
  measureQubit : {n : Nat} -> (1 _ : Qubit) -> QStateT (t (S n)) (t n) Bool

  ||| Same as measure, but with an initial state of n + i instead of i + n qubits to help with theorem proving in some cases
  -- public export
  -- measure2 : {n : Nat} -> {i : Nat} -> (LVect i Qubit) -> QStateT (t (n + i)) (t n) (Vect i Bool)
  -- measure2 v = rewrite plusCommutative n i in measure v

  ||| Measure all qubits in a quantum state
  ||| Because of a bug in Idris2, we use the implementation below.
  ||| However, the implementation commented out is preferable if the bug gets fixed.
  public export
  measureAll : {n : Nat} -> (1 _ : LVect n Qubit) -> QStateT (t n) (t 0) (Vect n Bool)

  --measureAll qs = rewrite sym $ plusZeroRightNeutral n in measure qs
                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  run : QStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)

|||Quantum circuit for the Quantum Fourier Transform

||| Auxiliary function for QFT : builds the recursive pattern
qftRecC : CombinedOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> UStateT (t (n+m)) (t (n+m)) (LVect n Qubit)
qftRecC 0 m [] = pure []
qftRecC 1 m [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecC (S (S k)) m (q::qs) = rewrite plusSuccRightSucc k m in do
        recwires <- qftRecC (S k) (S m) (qs)
        app <- applyUnitary (q::recwires) (cRmNRev (S (S k)))
        pure (app)
{-
qftRec : QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t (n+m)) (t (n+m)) (LVect n Qubit)
qftRec 0 m [] = pure []
qftRec 1 m [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRec (S (S k)) m (q::qs) = rewrite plusSuccRightSucc k m in do
        recwires <- qftRec (S k) (S m) (qs)
        app <- applyUnitary (q::recwires) (cRmNRev (S (S k)))
        pure (app)
  

||| QFT unitary circuit for n qubits
|||
||| n -- number of qubits
export
qft : (n : Nat) -> Unitary n
qft 0 = IdGate
qft (S k) = 
  let g = qftRec (S k)
      h = (IdGate {n = 1}) # (qft k)
  in h . g

qftQ : QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t (n+m)) (t (n+m)) (LVect n Qubit)
qftQ 0 m []= pure []
qftQ (S k) m (q::qs)= do
  h <- (qft k m qs)
  rec <- qftRec (S k) m (q::h)
  pure rec
  {-
  quantum_operation4 : QuantumOp t => IO (Vect 3 Bool)
  quantum_operation4 = 
    run (do
        [q1,q2] <- newQubits {t=t} 2                      --create 2 new qubits q1 and q2
        [q1,q2] <- applyUnitary [q1,q2] toBellBasis       --apply the toBellBasis unitary circuit to q1 and q2
        q3 <- newQubit                                    --create 1 new qubit q3
        [q1,q3,q2] <- applyUnitary [q1,q3,q2] toffoli     --apply toffoli gate on q1, q3 and q2
        [b2] <- measure [q2]                              --measure q2
        (q3 # q1) <- applyCNOT q3 q1                      --apply CNOT on q3 and q1
        [b1,b3] <- measure [q1,q3]                        --measure q1 and q3
        pure [b1,b2,b3]                                   --return the results
    ) -}