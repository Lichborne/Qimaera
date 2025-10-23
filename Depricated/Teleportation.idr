module Teleportation

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import QuantumOp
import LinearTypes
import UnitaryOp
import UStateT
import QStateT
import UnitaryLinear
import Qubit
import Examples

%default total

||| Example : Teleportation protocol

||| The unitary circuit that we have to apply to the initial state.
export
telep1 : UnitaryOp t => (1_ : LVect 3 Qubit) -> UStateT (t 3) (t 3) (LVect 3 Qubit)
telep1 [q0,q1,q2] = do
      [q1,q2] <- applyUnitary [q1,q2] toBellBasis
      [q0, q1] <- applyCNOT q0 q1
      [q0] <- applyH q0 
      pure [q0,q1,q2]

||| The unitary correction that has to be applied after performing the measurement in the Bell basis.
||| The two Bool arguments indicate the measurement results.
export
unitary_correction : UnitaryOp t => Bool -> Bool -> (1_ : LVect 1 Qubit) -> UStateT (t 1) (t 1) (LVect 1 Qubit)
unitary_correction True True q = do 
    q <- applyUnitary q XGate
    q <- applyUnitary q IdGate
    pure q
unitary_correction False True q = do
    q <- applyUnitary q ZGate
    pure q
unitary_correction True False q = do 
    q <- applyUnitary q XGate
    pure q
unitary_correction False False q = pure q
  


||| The Quantum Teleportation Protocol as a state transformer.
export
teleportation : UnitaryOp t => QuantumOp t =>
                (1 _ : Qubit) -> QStateT (t 1) (t 1) Qubit
teleportation q0 = do
  [q1, q2] <- newQubits {t=t} 2
  [q0,q1,q2] <- applyUST {t=t} (telep1 {t = t} [q0,q1,q2])
  [b0, b1] <- measure {t=t} [q0,q1]
  [q] <- applyUST {t=t} $ (unitary_correction {t = t} b0 b1 [q2]) 
  pure q
  
||| Run the teleportation protocol two times on specific input states
export
exampleTeleportation : UnitaryOp t => QuantumOp t => IO (Vect 2 Bool)
exampleTeleportation = runQ {t = t} (do
        q <- newQubit {t = t}
        [q] <- applyUST {t = t} $ applyH q
        q <- teleportation {t = t} q
        [b1] <- measure {t = t} [q]
        -- Second teleportation run
        q <- newQubit {t = t}
        [q] <- applyUST {t = t} $ applyUnitary [q] XGate
        q <- teleportation {t = t} q
        [b2] <- measure {t = t} [q]
        pure [b1,b2]
      )

exampleTeleTest : UnitaryOp t => QuantumOp t => IO (Vect 2 Bool)
exampleTeleTest = do
  bs <- exampleTeleportation {t = SimulatedOp}
  pure bs