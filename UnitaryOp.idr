module UnitaryOp

import Data.Vect
import Data.Nat
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Lemmas
import Unitary
--import QStateT
--import Control.Linear.LIO
import LinearTypes
--import Unitary

||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.

||| The UnitaryOp interface is used to abstract over the representation of a
||| unitarz operation. It is parameterised by the number of qubits it contains.
export
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Apply a Unitary to another smaller one
  applyU : {n : Nat} -> {i : Nat} -> Unitary n -> {auto prf: LT i n} -> {auto valid: LTE 2 n} -> UStateT (Unitary i) (Unitary n) ((Vect i (Fin n)))
  applyU ui un q = do
    wires <- get
    [q1] <- apply {n = n} {i = rewrite (sym $ comeOnIdrisGen {n=n} {m=i} {prf = lteSuccLeft prf}) in (justFinLemma i (minus n i) {prf = rewrite lteSuccLeft in valid})}
              ui un wires  {valid = valid}
    pure q1 

  |||
  tensorU : {n : Nat} -> {p : Nat} -> Unitary n -> Unitary p -> UStateT (Vect 0 Fin n) (Vect n+p (Fin (n+p))) (Unitary (n+p))
  tensorU ui un = do
    [q1] <- tensor ui un
    pure q1 

                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  run : UStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)