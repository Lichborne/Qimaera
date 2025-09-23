module QFT

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
import Lemmas
import SimulatedCircuitAlt
--import UnitaryOpTracked
--import QuantumOpTracked

%default total

|||Quantum circuit for the Quantum Fourier Transform

--CONTROLLED PHASE GATES FOR THE QFT

||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))

public export
||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

||| Builds the UnitaryOp with one's opwn version of a unitary; in our case this is of course UnitaryNoPrf or SimulatedOp 
RmOwn : UnitaryOp t => {n:Nat} -> Nat -> (1_: Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
RmOwn m q = do
  q <- applyP (2 * pi / (pow 2 (cast m))) q
  pure q

||| Builds the UnitaryOp (abstract) version of cRm
cRmAbs : UnitaryOp t => {n:Nat} -> Nat -> (1_: Qubit) -> (1_: Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
cRmAbs {n = Z} m c u = pure [c, u] -- this is if t n is empty, which cannot be the case if we have two qubits
cRmAbs {n = S k} m c u = do 
                cu <- applyControlledAbs c (RmOwn {n = k} m u)
                pure cu

||| Builds the rotation operator for the QFT inside UnitaryOp using the unitaries built with Unitary
rotate : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotate m q [] = pure (q :: [])
rotate {n} {i = (S k)} m q (p::ps) = do
        (p' :: [q']) <- applyUnitary (p :: [q]) (cRm m)
        (q'' :: ps') <- rotate (S m) q' ps
        pure (q'':: p':: ps')

||| Builds the whole operator for the QFT inside UnitaryOp using rotation using the unitaries built with Unitary
public export
qftU :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftU [] = pure []
qftU {n} {i = S k} (q::qs) = do
    (q' :: Nil ) <- applyUnitary [q] HGate
    (q'' :: qs') <- rotate (S (S Z)) q' qs
    qs'' <- qftU qs'
    pure (q'' :: qs'')

||| Full, partially abstract QFT
public export
qftQ : UnitaryOp t => QuantumOp t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftQ i n qs = applyUST {t=t} (qftU {t=t} {i = i} {n = n} (qs))

||| Builds the *abstract* rotation operator for the QFT inside UnitaryOp
rotateAbs : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotateAbs m q [] = pure (q :: [])
rotateAbs {n} {i = (S k)} m q (p::ps) = do
        (p' :: [q']) <- cRmAbs m p q
        (q'' :: ps') <- rotateAbs (S m) q' ps
        pure (q'':: p':: ps')

||| Builds the *abstract* operator for the QFT inside UnitaryOp using rotation
public export
qftUAbs :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftUAbs [] = pure []
qftUAbs {n} {i = S k} (q::qs) = do
    [q']<- applyH q
    (q'' :: qs') <- rotateAbs (S (S Z)) q' qs
    qs'' <- qftUAbs qs'
    pure (q'' :: qs'')

||| Full, fully abstract QFT
public export
qftQAbs : UnitaryOp t => QuantumOp t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftQAbs i n qs = applyUST {t=t} (qftUAbs {t=t} {i = i} {n = n} (qs))


||| Builds the rotation operator for the QFT inside UnitaryOp using the unitaries built with Unitary
rotateInvManual : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotateInvManual m q [] = pure (q :: [])
rotateInvManual {n} {i = (S k)} m q (p::ps) = do
        (q' :: ps') <- rotateInvManual (S m) q ps
        (p' :: [q'']) <- applyUnitary (p :: [q']) (adjoint (cRm m))
        pure (q'':: p':: ps')

||| Builds the whole operator for the QFT inside UnitaryOp using rotation using the unitaries built with Unitary
public export
qftUInvManual :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftUInvManual [] = pure []
qftUInvManual {n} {i = S k} (q::qs) = do
    qs' <- qftUInvManual qs
    (q' :: qs'') <- rotateInvManual (S (S Z)) q qs'
    (q'' :: Nil ) <- applyUnitary [q'] (adjoint HGate)
    pure (q'' :: qs'')

||| suggested method for inverting UnitaryOp- build unitaries   
public export 
qftUInv : UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftUInv lvect = invertUST (qftU lvect)

||| Full, partially abstract QFT
public export
qftQInv : UnitaryOp t => QuantumOp t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftQInv i n qs = applyUST {t=t} (qftUInv {t=t} {i = i} {n = n} (qs))

---------------------- TESTS ------------------------

public export
||| Run with 3 qubits with SimulatedOp(any more takes too long on a normal computer)
runQFTAbs3 : UnitaryOp t => QuantumOp t => IO (Vect 3 Bool)
runQFTAbs3 = runQ {t=t} (do
    qs <- newQubits 3 {t = t}
    qfts <- qftQAbs {t=t} 3 3 qs 
    measureAll qfts
    )
public export
||| Test with 3 qubits with SimulatedOp(any more takes too long on a normal computer) 
testQFTAbs3 : IO (Vect 3 Bool)
testQFTAbs3 = (do
  bs <- runQFTAbs3 { t = SimulatedOp }
  pure bs)

public export 
||| Run with 12 qubits with SimulatedCircuit
runQFTAbs12 : UnitaryOp t => QuantumOp t => IO (Vect 12 Bool)
runQFTAbs12 = runQ {t=t} (do
    qs <- newQubits 12 {t = t}
    qfts <- qftQAbs {t=t} 12 12 qs 
    measureAll qfts)

public export
||| Test with 12 qubits with SimulatedCircuit
testQFTAbs12 : IO (Vect 12 Bool)
testQFTAbs12 = (do
  bs <- runQFTAbs12 { t = SimulatedCircuit}
  pure bs)
