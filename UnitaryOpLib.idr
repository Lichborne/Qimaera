module UnitaryOpLib

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

pairL : LPair a b -> Pair a b
pairL (a # b) = MkPair a b

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
-----------------------------------------------------

||| Prepare a single new Wire in state |0>
partial
firstWire : {n:Nat} -> UStateT (Unitary 0) (Unitary 0) (LVect 1 Wire)
firstWire {n} = --rewrite sym $ lemmaplusOneRight n in     
    do
        pure (MkWire (0)::Nil)

newWire : {n:Nat} -> {m:Nat} -> UStateT (Unitary n) (Unitary n) (LVect (S n) Wire)
newWire {n=0} = --rewrite sym $ lemmaplusOneRight n in     
    do
        firstWire
newWire {n= S k} = do
            pre <- newWire {n = k}
            pure (pre ++ MkWire (S k))

||| Prepare 'p' new Wires in state |00...0>
public export
newWires : {n : Nat} -> (p : Nat) -> UStateT (Unitary n) (Unitary (n+p)) (LVect (n+p) Wire)
newWires Z     = rewrite plusZeroRightNeutral n in pure []
newWires {n} (S k) = rewrite lemmaPlusSRight n k in do
    q <- newWire {n = n + S k}
    qs <- newWires k
    pure (LinearTypes.(::) q qs)

||| Apply a unitary circuit to the Wires specified by the Vect argument
applyUnitary : {n : Nat} -> {i : Nat} ->
            (1 _ : LVect i Wire) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Wire)
applyUnitary v ui = do


||| Apply the Hadamard gate to a single Wire
applyH : {n : Nat} -> (1 _ : Wire) -> UStateT (Unitary n) (Unitary n) Wire
applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure q1

||| Apply a P gate to a single Wire
applyP : {n : Nat} -> Double -> (1 _ : Wire) -> UStateT (Unitary n) (Unitary n) Wire
applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure q1

||| Apply the CNOT gate to a pair of Wires
applyCNOT : {n : Nat} -> (1 _ : Wire) -> (1 _ : Wire) -> UStateT (Unitary n) (Unitary n) (LPair Wire Wire)
applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1 # q2)

||| Execute a quantum operation : start and finish with trivial quantum state
||| (0 Wires) and measure 'n' Wires in the process
run : (1 _ : t 0) -> (1 _ : UStateT (Unitary 0) (Unitary n) (LVect n Wire) ) -> R (LPair (Unitary n) (LVect n Wire))
run u0 ust = runUStateT u0 ust