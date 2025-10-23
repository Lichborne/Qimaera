module QFT2

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
import UnitaryOpTracked
import QuantumOpTracked
import Qubit

%default total

|||Quantum circuit for the Quantum Fourier Transform

--CONTROLLED PHASE GATES FOR THE QFT

||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))

||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

--applyControlledRm : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair Qubit Qubit)
--applyCNOT q1 q2 = do
  --[q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) (controlled (PGate (2 * pi / (pow 2 (cast m)))))
  --pure (q1 # q2)

--QFT

cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S m)) = apply (cRm (S (S m))) (tensorn (S (S m)) IdGate) [0, (S m)] 

||| tracking the unitaries
qftRecUT : UnitaryOpT t => (i : Nat) -> (n:Nat) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LPair (Unitary i) (LVect i Qubit))
qftRecUT 0 n [] = pure (IdGate # [])
qftRecUT 1 n [w] = do
        u # wh <- applyH w
        pure $ u # ((::) wh LinearTypes.Nil)
qftRecUT (S k) n (q::qs) = let u = cRmNRev (S k) in do 
        (us # recwires) <- qftRecUT k n (qs)
        uss # app <- applyUnitaryT n (S k) (q::recwires) (u)
        pure ((compose {n = S k} uss (tensor {n = 1} IdGate us)) # app) 

qftT : UnitaryOpT t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (Unitary i) (LVect i Qubit))
qftT 0 n any = pure (IdGate # any)
qftT (S k) n (q::qs) = qftRecUT (S k) n (q::qs) >>= \(u # l::ls) => qftT k n (ls) >>= \(us # fs) => pure $ (composeN {n = (S k)} u (tensor {n = 1} IdGate us)) # (l::fs)

test : UnitaryOpT t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (Unitary i) (LVect i Qubit))
test i n qs = (qftT {t = t} i n (qs))

qftQT : UnitaryOpT r => QuantumOpT t =>  (i : Nat) ->  (n: Nat)-> (1 _ : LVect i Qubit) -> QStateT (t (n)) (t (n)) (LPair (Unitary i) (LVect i Qubit))
qftQT i n qs = QuantumOpTracked.applyUnitaryT {t = t} {r = r} n i (believe_me $ qftT {t = r} i n (qs))


patternRecT : UnitaryOpT t => (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) -> 
        (1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LPair (Unitary n) (LVect n Qubit))
patternRecT 0 m unitary baseCaseUnitary [] = pure (IdGate # [])
patternRecT 1 m unitary baseCaseUnitary [w] = do
        u # wh <- applyUnitaryT m 1 [w] baseCaseUnitary
        pure $ u # wh
patternRecT (S k) m unitary baseCaseUnitary (q::qs) = do
        (us # recwires) <- patternRecT k m unitary baseCaseUnitary (qs)
        uss # app <- applyUnitaryT m (S k) (q::recwires) (unitary (S k))
        pure ((compose {n = S k} uss (tensor {n = 1} IdGate us)) # app) 

patternRecDoubleT : UnitaryOpT t => (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) -> 
(1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LPair (Unitary n) (LVect n Qubit))
patternRecDoubleT 0 m unitary bCU qs = pure (IdGate # qs)
patternRecDoubleT (S k) m unitary bCU (q::qs) = do
        u # l::ls <- patternRecT (S k) m unitary bCU (q::qs)
        us # fs <- patternRecDoubleT k m unitary bCU (ls) 
        pure $ (compose u (tensor IdGate {n = 1} us)) # (l::fs)

patternQ : UnitaryOpT r => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
(pattern: ( (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) 
                -> (1 _ : LVect n Qubit) -> UStateT (r m) (r m) (LPair (Unitary n) (LVect n Qubit)))) ->
(1_ : LVect n Qubit) -> QStateT (t m) (t m) (LPair (Unitary n) (LVect n Qubit))
patternQ n m bCU u pat qs = QuantumOpTracked.applyUnitaryT {r = r} m n (believe_me $ pat n m u bCU qs)
{-}
patternQSingle : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
(1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQSingle n m bCU u qs = patternQ {r = r} {t = t} n m bCU u (patternRec) qs

patternQDouble : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
(1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQDouble n m bCU u qs = patternQ {r = r} {t = t} n m bCU u (patternRecDouble) qs

patternQFT : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQFT n m qs = patternQDouble {r = r} {t = t} n m HGate cRmNRev qs
      

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