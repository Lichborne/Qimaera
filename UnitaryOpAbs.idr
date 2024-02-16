module CombinedOp

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

consLinW : (1 _ : Wire) -> (1 _ : Vect n Wire) -> Vect (S n) Wire
consLinW (MkWire Z) [] = [(MkWire Z)]
consLinW (MkWire Z) (x :: xs) = (MkWire Z) :: x :: xs
consLinW ((MkWire (S k))) [] = [MkWire (S k)]
consLinW (MkWire (S k)) (x :: xs) = (MkWire (S k)) :: x :: xs

nilToLNIL : (1 _ : Vect 0 Wire) -> LVect 0 Wire
nilToLNIL [] = []

toVectW : {n:Nat} -> (1 _ : LVect n Wire) -> Vect n Wire
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

natReV : (1 _ : Vect n Wire) -> Vect n Nat
natReV [] = []
natReV (MkWire any::ws) = any :: (natReV ws)

private
%hint
natReVLemma : (v:Vect n Wire) -> (v':Vect p Wire)-> natReV v ++ natReV v' = natReV (v ++ v')
natReVLemma v w = believe_me ()

--duplicateVectN : {n:Nat} -> (1 _ :  (Vect n Nat)) -> Pair (Vect n Nat) (Vect n Nat)
--duplicateVectN [] = MkPair [] []
--duplicateVectN (x::xs) = MkPair (x::(fst $ duplicateVect xs)) (x::(snd $ duplicateVect xs))

takeNmOneL : (1 _ : LVect (S n) Wire) -> (LVect n Wire)
takeNmOneL [q] = nilToLNIL $ takeOneV1 (toVectW [q]) 
takeNmOneL (q::qs::qss) = q :: takeNmOneL (qs::qss)
-----------------------------------------------------


||| The UnitaryOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Wires it contains.
export
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Wires specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Wire) -> Unitary i -> UStateT (t n) (t n) (LVect i Wire)

  ||| Apply the Hadamard gate to a single Wire
  applyH : {n : Nat} -> (1 _ : Wire) -> UStateT (t n) (t n) Wire
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure q1

  ||| Apply a P gate to a single Wire
  applyP : {n : Nat} -> Double -> (1 _ : Wire) -> UStateT (t n) (t n) Wire
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure q1

  ||| Apply the CNOT gate to a pair of Wires
  applyCNOT : {n : Nat} -> (1 _ : Wire) -> (1 _ : Wire) -> UStateT (t n) (t n) (LPair Wire Wire)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1 # q2)

  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 Wires) and measure 'n' Wires in the process
  run : (1 _ : t 0) -> (1 _ : UStateT (t 0) (t n) (LVect n Wire) ) -> R (LPair (t n) (LVect n Wire))
  run u0 ust = runUStateT u0 ust
