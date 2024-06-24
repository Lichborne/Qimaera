module QFT

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import Lemmas
import QuantumOp
import LinearTypes
import UnitaryOp
import UStateT
import QStateT
import UnitaryLinear

%default total

|||Quantum circuit for the Quantum Fourier Transform

--CONTROLLED PHASE GATES FOR THE QFT

||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))


||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)


--QFT

cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S m)) = apply (cRm (S (S m))) (tensorn (S (S m)) IdGate) [0, (S m)] 

qftRecU : UnitaryOp t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (m)) (t (m)) (LVect i Qubit)
qftRecU {i = 0} {m = m} [] = pure []
qftRecU {i = 1} {m = m} [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecU {i = (S k)} {m = m}  (q::qs) = let u = cRmNRev (S k) in do 
        recwires <- qftRecU {i = k} {m = m} (qs)
        app <- UnitaryOp.applyUnitary {n = m} {i = (S k)} (q::recwires) (u)
        pure (app) 

export 
qft : UnitaryOp t => (i : Nat) -> (m: Nat) -> (1 _ : LVect i Qubit) -> UStateT (t m) (t m) (LVect i Qubit)
qft 0 m any = pure any
qft (S k) m (q::qs) = qftRecU {i =(S k)} {m = m} (q::qs) >>= \(l::ls) => qft k m (ls) >>= \fs => pure (l::fs)


qftQ : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t (m)) (t (m)) (LVect n Qubit)
qftQ n m qs = applyUnitary (qft {t=r} n m (qs))

{-
DEPRICATED

||| Classical: Auxiliary function for QFT : builds the recursive pattern
|||
||| n -- number of qubits
export
qftRec : (n : Nat) -> Unitary n
qftRec 0 = IdGate
qftRec 1 = HGate
qftRec (S (S k)) = 
  let t1 = tensor (qftRec (S k)) IdGate
  in rewrite sym $ lemmaplusOneRight k in apply (cRm (S (S k))) t1 [S k, 0] 


cRmNRevSS : (k:Nat) -> Unitary (S (S k))
cRmNRevSS m = apply (cRm (S (S m))) (tensorn (S (S m)) IdGate) [0, (S m)] 

qftQFull : QuantumOp t => (n : Nat) -> (m: Nat) -> QStateT (t (m)) (t (m)) (LVect n Qubit)
qftQFull 0 m = pure []
qftQFull (S k) m = let qqs = (toVectW qs) in do
        qs <- newQubits (S k)
        qftqs <- applyUnitary $ UnitaryOp.run (qft {i = (S k)} {m = m} (qqs))
        pure qftqs
                     


qftRecU : QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t (n+m)) (t (n+m)) (LVect n Qubit)
qftRecU 0 m [] = pure []
qftRecU 1 m [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecU (S (S k)) m (q::qs) = rewrite plusSuccRightSucc k m in do
        recwires <- qftRecU (S k) (S m) (qs)
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




--A FEW LEMMAS FOR THE QFT

kLTSucc1 : (k : Nat) -> k < (k + 1) = True
kLTSucc1 0 = Refl
kLTSucc1 (S k) = kLTSucc1 k

lemmaInj1 : (k : Nat) -> isInjective (S (k + 1)) [S k, 0] = True
lemmaInj1 k = 
  let p1 = kLTSucc1 k
  in lemmaAnd (lemmaAnd p1 Refl) Refl

consLinW : (1 _ : Qubit) -> (1 _ : Vect n Qubit) -> Vect (S n) Qubit
consLinW (MkQubit Z) [] = [(MkQubit Z)]
consLinW (MkQubit Z) (x :: xs) = (MkQubit Z) :: x :: xs
consLinW ((MkQubit (S k))) [] = [MkQubit (S k)]
consLinW (MkQubit (S k)) (x :: xs) = (MkQubit (S k)) :: x :: xs

nilToLNIL : (1 _ : Vect 0 Qubit) -> LVect 0 Qubit
nilToLNIL [] = []

toVectW : {n:Nat} -> (1 _ : LVect n Qubit) -> Vect n Qubit
toVectW [] = []
toVectW (x :: xs) = x `consLinW` (toVectW xs)
-}