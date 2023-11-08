module Side

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

-----Auxiliaries ------
export
data Wire : Type where
  MkWire : (n : Nat) -> Wire

data t : Nat -> Type

consLinW : (1 _ : Wire) -> (1 _ : Vect n Wire) -> Vect (S n) Wire
consLinW (MkWire Z) [] = [(MkWire Z)]
consLinW (MkWire Z) (x :: xs) = (MkWire Z) :: x :: xs
consLinW ((MkWire (S k))) [] = [MkWire (S k)]
consLinW (MkWire (S k)) (x :: xs) = (MkWire (S k)) :: x :: xs

nilToLNIL : (1 _ : Vect 0 Wire) -> LVect 0 Wire
nilToLNIL [] = []

toVectW : (1 _ : LVect n Wire) -> Vect n Wire
toVectW [] = []
toVectW (x :: xs) = x `consLinW` (toVectW xs)

consWV : (1 _ : Wire) -> (1 _ : Vect n Wire) -> LVect (S n) Wire
consWV (MkWire Z) [] = [(MkWire Z)]
consWV (MkWire Z) (x :: xs) = (MkWire Z) :: (consWV x xs)
consWV ((MkWire (S k))) [] = [MkWire (S k)]
consWV (MkWire (S k)) (x :: xs) = (MkWire (S k)) :: (consWV x xs)

toLVectW : (1 _ : Vect n Wire) -> LVect n Wire
toLVectW [] = []
toLVectW (x :: xs) = x `consWV` xs

takeOneV1 : (1 _ : Vect (S n) Wire) -> (Vect n Wire)
takeOneV1 [q] = []
takeOneV1 (q::qs::qss) = q :: takeOneV1 (qs::qss)

duplicateVect : {n:Nat} -> (1 _ :  (Vect n Wire)) -> LPair (Vect n Wire) (Vect n Wire)
duplicateVect [] = [] # []
duplicateVect {n = S k} (x::xs) = (x::xs) # (x::xs)

--duplicateVectN : {n:Nat} -> (1 _ :  (Vect n Nat)) -> Pair (Vect n Nat) (Vect n Nat)
--duplicateVectN [] = MkPair [] []
--duplicateVectN (x::xs) = MkPair (x::(fst $ duplicateVect xs)) (x::(snd $ duplicateVect xs))

takeNmOneL : (1 _ : LVect (S n) Wire) -> (LVect n Wire)
takeNmOneL [q] = nilToLNIL $ takeOneV1 (toVectW [q]) 
takeNmOneL (q::qs::qss) = q :: takeNmOneL (qs::qss)
-----------------------------------------------------




||| Prepare 'p' new Wires in state |00...0>
newWires : (p : Nat) -> UStateT (t n) (t (n+p)) (Vect p Wire)
newWires Z     = rewrite plusZeroRightNeutral n in pure []
newWires (S k) = rewrite lemmaPlusSRight n k in do
q <- newWire
qs <- newWires k
pure (toVectW $ LinearTypes.(::) q (toLVectW qs))

||| Prepare a single new Wire in state |0>
newWire : UStateT (t n) (t (S n)) Wire
newWire = rewrite sym $ lemmaplusOneRight n in do
[q] <- newWires 1
pure q

||| Apply a unitary circuit to the Wires specified by the Vect argument
applyUnitary : {n : Nat} -> {i : Nat} ->
                (1 _ : Vect i Wire) -> Unitary i -> UStateT (t n) (t n) (Vect i Wire)

applyUnitaryL : {n : Nat} -> {i : Nat} ->
(1 _ : LVect i Wire) -> Unitary i -> UStateT (t n) (t n) (LVect i Wire)

||| Apply the Hadamard gate to a single Wire
applyH : {n : Nat} -> (1 _ : Wire) -> UStateT (t n) (t n) Wire
applyH q = do
[q1] <- applyUnitary {n} {i = 1} (toVectW [q]) HGate 
pure q1

||| Apply a P gate to a single Wire
applyP : {n : Nat} -> Double -> (1 _ : Wire) -> UStateT (t n) (t n) Wire
applyP p q = do
[q1] <- applyUnitary {n} {i = 1} (toVectW [q]) (PGate p)
pure q1

||| Apply the CNOT gate to a pair of Wires
applyCNOT : {n : Nat} -> (1 _ : Wire) -> (1 _ : Wire) -> UStateT (t n) (t n) (LPair Wire Wire)
applyCNOT q1 q2 = do
[q1,q2] <- applyUnitary {n} {i = 2} (toVectW [q1,q2]) CNOTGate
pure (q1 # q2)

||| Execute a quantum operation : start and finish with trivial quantum state
||| (0 Wires) and measure 'n' Wires in the process
run : UStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)


||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))


||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

cRmN : (n:Nat) -> Unitary n
cRmN 0 = IdGate
cRmN 1 = IdGate
cRmN (S (S k)) = apply (cRm (S (S k))) (tensorn (S (S k)) IdGate) [S k, 0]

cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S k)) = apply (cRm (S (S k))) (tensorn (S (S k)) IdGate) [0, (S k)]

fExp : (1 _ : (1 _ : Unitary n) -> R (LPair (Unitary (S n)) (LVect (S n) Wire))) -> ((1 _ : Unitary (S n))-> R (LPair (Unitary (S n)) (LVect (S n) Wire)))
fExp g = ?what

pushup:{n:Nat} -> (1 _ : UStateT (Unitary n) (Unitary (S n)) (LVect (S n) Wire)) -> UStateT (Unitary (S n)) (Unitary (S n)) (LVect (S n) Wire)
pushup (MkUST f) = MkUST (\x => (fExp f) x)

natRe : (1 _ : Wire) -> Nat
natRe (MkWire Z) = Z
natRe (MkWire (S k)) = S k

qftUnitarySafe : (n : Nat) -> (1 _ : Vect n Wire) -> Unitary n
qftUnitarySafe 0 [] = IdGate
qftUnitarySafe 1 [w] = HGate
qftUnitarySafe (S (S k)) (qs) = let t1 = tensor (qftUnitarySafe (S k) (takeOneV1 (qs))) IdGate in 
                                    rewrite sym $ lemmaplusOneRight k in
                                      apply (cRm (S (S k))) t1 [S k, 0]

qftRec : (n : Nat) -> (1 _ : Vect n Wire) -> UStateT (Unitary n) (Unitary n) (Vect n Wire)
qftRec Z [] = pure []
qftRec (S m) (w::ws) = do
  q <- applyUnitary (w::ws) (qftUnitarySafe (S m) (w::ws))
  pure q

qftR : (n : Nat) -> UStateT (Unitary 0) (Unitary n) (Vect n Wire)
qftR 0 = pure []
qftR (S k) = do
  (w::ws) <- newWires (S k)
  out <- qftRec (S k) (w::ws)
  pure out

------------------------------------
{-}
qftRecRev2 : UnitaryOp Unitary => (n : Nat) -> UStateT (Unitary 0) (Unitary n) (LVect n Wire)
qftRecRev2 0 = pure []
qftRecRev2 1 = do
        w <- newWire
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecRev2 (S (S k)) = do
  recwires  <- qftRecRev2 (S k)
  app <- applyUnitaryL recwires (cRmNRev (S k))
  pure app


  qftRec : (n : Nat) -> Unitary n
  qftRec 0 = IdGate
  qftRec 1 = HGate
  qftRec (S (S k)) = 
    let t1 = (qftRec (S k)) # IdGate
    in rewrite sym $ lemmaplusOneRight k in apply (cRm (S (S k))) t1 [S k, 0] 

qftRecRev : UnitaryOp Unitary => (n : Nat) -> (1 _ : LVect n Wire) -> UStateT (Unitary n) (Unitary n) (LVect n Wire)
qftRecRev 0 [] = pure []
qftRecRev 1 [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecRev (S (S k)) (q::qs) = qftRecRev (S k) (qs) >>= (\recwires => applyUnitary (q::recwires) (cRmNRev (S (S k)))) >>= (\app => pure (app))

qftRec : UnitaryOp Unitary => (n : Nat) -> (1 _ : LVect n Wire) -> UStateT (Unitary n) (Unitary n) (LVect n Wire)
qftRec 0 [] = pure []
qftRec 1 [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRec (S (S k)) (q::qs) = rewrite sym $ lemmaplusOneRight k in do
        recwires <- qftRec (S k) (takeNmOneL (q::qs))
        plus <- newWire
        applied <- applyUnitary (recwires++[plus]) (cRmN (S (S k)))
        pure applied
      
qftRec0 : UnitaryOp Unitary => UStateT (Unitary 0) (Unitary 0) (LVect 0 Wire)
qftRec0 = pure []


qftRec1 : UnitaryOp Unitary => UStateT (Unitary 1) (Unitary 2) (LVect 1 Wire)
qftRec1 = do
    w <- newWire
    wh <- applyH w
    pure $ (::) wh LinearTypes.Nil 

qftRecSSk : UnitaryOp Unitary => (n : Nat) -> UStateT (Unitary n) (Unitary n) (LVect n Wire)
qftRecSSk (S (S k)) = rewrite sym $ lemmaplusOneRight k in do
        wires <- qftRecSSk (S k)
        applied <- applyUnitary wires (cRm (S (S k)))
        pure applied
-}

