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

||| Run with 3 qubits (any more takes too long on a normal computer)
runQFTAbs3 : UnitaryOp t => QuantumOp t => IO (Vect 3 Bool)
runQFTAbs3 = runQ {t=t} (do
    qs <- newQubits 3 {t = t}
    qfts <- qftQAbs {t=t} 3 3 qs 
    measureAll qfts
    )

||| Test with 3 qubits (any more takes too long on a normal computer) 
testQFTAbs3 : IO (Vect 3 Bool)
testQFTAbs3 = (do
  bs <- runQFTAbs3 { t = SimulatedOp }
  pure bs)


||| Builds the rotation operator for the QFT inside UnitaryOp using the unitaries built with Unitary
rotateInv : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotateInv m q [] = pure (q :: [])
rotateInv {n} {i = (S k)} m q (p::ps) = do
        (q' :: ps') <- rotate (S m) q ps
        (p' :: [q'']) <- applyUnitary (p :: [q']) (adjoint (cRm m))
        pure (q'':: p':: ps')

||| Builds the whole operator for the QFT inside UnitaryOp using rotation using the unitaries built with Unitary
public export
qftUInv :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftUInv [] = pure []
qftUInv {n} {i = S k} (q::qs) = do
    qs' <- qftUInv qs
    (q' :: qs'') <- rotate (S (S Z)) q qs'
    (q'' :: Nil ) <- applyUnitary [q'] (adjoint HGate)
    pure (q'' :: qs'')

||| Full, partially abstract QFT
public export
qftQInv : UnitaryOp t => QuantumOp t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftQInv i n qs = applyUST {t=t} (qftUInv {t=t} {i = i} {n = n} (qs))



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
cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S m)) = apply (cRm (S (S m))) (tensorn (S (S m)) IdGate) [0, (S m)] 

qftRecU : UnitaryOp t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (m)) (t (m)) (LVect i Qubit)
qftRecU {i = 0} {m = m} [] = pure []
qftRecU {i = 1} {m = m} [w] = do
        wh <- UnitaryOp.applyH w
        pure $ wh
qftRecU {i = (S k)} {m = m}  (q::qs) = let u = cRmNRev (S k) in do 
        recwires <- qftRecU {i = k} {m = m} (qs)
        app <- UnitaryOp.applyUnitary {n = m} {i = (S k)} (q::recwires) (u)
        pure (app) 

export 
qft : UnitaryOp t => (i : Nat) -> (m: Nat) -> (1 _ : LVect i Qubit) -> UStateT (t m) (t m) (LVect i Qubit)
qft 0 m any = pure any
qft (S k) m (q::qs) = qftRecU {t=t} {i =(S k)} {m = m} (q::qs) >>= \(l::ls) => qft k m (ls) >>= \fs => pure (l::fs)

||| QFT unitary circuit for n qubits
|||
||| n -- number of qubits
export
:

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
--applyControlledRm : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LPair Qubit Qubit)
--applyCNOT q1 q2 = do
  --[q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) (controlled (PGate (2 * pi / (pow 2 (cast m)))))
  --pure (q1 # q2)

--QFT
{-}
cRmNRevAbs : UnitaryOp t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (m)) (t (m)) (LVect i Qubit)

qftRecAbs : UnitaryOp t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (m)) (t (m)) (LVect i Qubit)
qftRecAbs {i = 0} {m = m} [] = pure []
qftRecAbs {i = 1} {m = m} [w] = do
        wh <- UnitaryOp.applyHAbs [w]
        pure $ wh
qftRecAbs {i = (S k)} {m = m}  (q::qs) = do
        recwires <- qftRecAbs {i = k} {m = m} (qs)
        app <- cRmNRevAbs (q::recwires)
        pure (app) 

qftAbs : UnitaryOp t => (i : Nat) -> (m: Nat) -> (1 _ : LVect i Qubit) -> UStateT (t m) (t m) (LVect i Qubit)
qftAbs 0 m any = pure any
qftAbs (S k) m (q::qs) = qftRecAbs {i =(S k)} {m = m} (q::qs) >>= \(l::ls) => qftAbs k m (ls) >>= \fs => pure (l::fs)
        
qftQAbs : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t (m)) (t (m)) (LVect n Qubit)
qftQAbs n m qs = applyUnitary (qftAbs {t=r} n m (qs))

------------------------------------------


patternRecAbs : UnitaryOp t => (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> t k) -> (baseCaseUnitary : t 1) -> 
  (1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LVect n Qubit)
patternRecAbs 0 m unitary baseCaseUnitary [] = pure LinearTypes.Nil
patternRecAbs 1 m unitary baseCaseUnitary [w] = do
          wh <- applytU [w] baseCaseUnitary
          pure $ wh
patternRecAbs (S k) m unitary baseCaseUnitary (q::qs) = do
          recwires <- patternRecAbs k m unitary baseCaseUnitary (qs)
          app <- applytU {n = m} {i = (S k)} (q::recwires) (unitary (S k))
          pure (app) 

patternRecDouble : UnitaryOp t => (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) -> 
  (1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LVect n Qubit)
patternRecDouble 0 m unitary bCU qs = pure qs
patternRecDouble (S k) m unitary bCU (q::qs) = do
  l::ls <- patternRec (S k) m unitary bCU (q::qs)
  fs <- patternRecDouble k m unitary bCU (ls) 
  pure (l::fs)

patternQ : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
  (pattern : ( (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) 
                -> (1 _ : LVect n Qubit) -> UStateT (r m) (r m) (LVect n Qubit))) ->
  (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQ n m bCU u pat qs = applyUnitary {r = r} (pat n m u bCU qs)

patternQSingle : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
  (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQSingle n m bCU u qs = patternQ {r = r} {t = t} n m bCU u (patternRec) qs

patternQDouble : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
  (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQDouble n m bCU u qs = patternQ {r = r} {t = t} n m bCU u (patternRecDouble) qs

patternQFT : UnitaryOp r => QuantumOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQFT n m qs = patternQDouble {r = r} {t = t} n m HGate cRmNRev qs


------------------------------------------
export
qftRec : (n : Nat) -> Unitary n
qftRec 0 = IdGate
qftRec 1 = HGate
qftRec (S (S k)) = 
  let t1 = (qftRec (S k)) # IdGate
  in rewrite sym $ lemmaplusOneRight k in apply (cRm (S (S k))) t1 [S k, 0] {prf = lemmaInj1 k}
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

  -}