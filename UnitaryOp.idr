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
import UState
--import QStateT
import Control.Linear.LIO
import LinearTypes
--import Unitary
%hide Prelude.(>>=)
||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.

||| The UnitaryOp interface is used to abstract over the representation of a
||| unitary operations. It is parameterised by the number of qubits it contains.


export
buildH : UState (Unitary 1) (Unitary 1) (Unitary 1) 
buildH = do 
  UState.pure HGate

export 
buildP : Double -> UState (Unitary 1) (Unitary 1) (Unitary 1) 
buildP p = do 
  UState.pure (PGate p)

export
buildID : UState (Unitary n) (Unitary n) (Unitary n)
buildID = do 
  UState.pure IdGate

export
tensorU : {n : Nat} -> {p : Nat} -> Unitary p -> UState (Unitary n) (Unitary n) (Unitary (n+p))
tensorU up = MkUS $ (\un => runUState un (UState.pure (tensor un up)))

export
tensorUF : {n : Nat} -> {p : Nat} -> Unitary p -> UState (Unitary n) (Unitary n) (Unitary (n+p))
tensorUF up = MkUS $ (\un => runUState un (UState.pure (tensor un up)))

private
tensorSepU : {n : Nat} -> {p : Nat} -> Unitary n -> Unitary p -> UState (Unitary n) (Unitary n) (Unitary (n+p))
tensorSepU un up = (UState.pure (tensor un up))

export 
composeU : {n : Nat} -> Unitary n -> UState (Unitary n) (Unitary n) (Unitary n)
composeU fst = MkUS $ (\un => runUState un (UState.pure (compose fst un)))

myFunc : UState (Unitary 1) (Unitary 1) (Unitary 3)
myFunc = do 
  id <- buildH
  t <- tensorU (PGate 1)
  p <- tensorSepU (PGate 2) t
  UState.pure p --?what
  

{-}
  ||| Apply a Unitary to another smaller one
  applyU : {n : Nat} -> {i : Nat} -> Unitary i -> {auto prf: LT i n} -> {auto valid: LTE 2 n} 
              -> UStateT (LPair (Unitary n) (DPair (v: Vect n Nat) (IsInjective n v))) (LPair (Unitary n) (DPair (v: Vect n Nat) (IsInjective n v))) (Unitary n)
  applyU un = do
    [q1] <- apply {n = n} {i = rewrite (sym $ comeOnIdrisGen {n=n} {m=i} {prf = lteSuccLeft prf}) in (justFinLemma i (minus n i) {prf = rewrite lteSuccLeft in valid})}
              ui un wires  {valid = valid}
    pure q1 
  

                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
            run : UStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool) -}