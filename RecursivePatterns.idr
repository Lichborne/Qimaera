module RecursivePatterns

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import Lemmas
import QuantumOp
import LinearTypes
--import UnitaryOp
import UStateT
import QStateT
import UnitaryLinear


%default total

|||Recursive patterns for building functions like the quantum Fourier transform more easily

|||----------------------------------------------------------------------------------------|||

||| Pattern for recursively building large unitaries from a base unitary and a function for getting a parametrized unitary from some k (like rotate)
patternRec : UnitaryOp t => (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) -> 
  (1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LVect n Qubit)
patternRec 0 m unitary baseCaseUnitary [] = pure LinearTypes.Nil
patternRec 1 m unitary baseCaseUnitary [w] = do
          wh <- applyUnitary [w] baseCaseUnitary
          pure $ wh
patternRec (S k) m unitary baseCaseUnitary (q::qs) = do
          recwires <- patternRec k m unitary baseCaseUnitary (qs)
          app <- applyUnitary {n = m} {i = (S k)} (q::recwires) (unitary (S k))
          pure (app) 

||| Outer pattern for recursively building large unitaries from a base unitary and a function for getting a parametrized unitary from some k (like qftU)
patternRecDouble : UnitaryOp t => (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) -> 
  (1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LVect n Qubit)
patternRecDouble 0 m unitary bCU qs = pure qs
patternRecDouble (S k) m unitary bCU (q::qs) = do
  l::ls <- patternRec (S k) m unitary bCU (q::qs)
  fs <- patternRecDouble k m unitary bCU (ls) 
  pure (l::fs)

||| Pattern for using a unitary building pattern and raising it to a QuantumOP (used below)  
patternQ : UnitaryOp t => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
  (pattern : ( (n : Nat) -> (m: Nat) -> (unitary : (k:Nat) -> Unitary k) -> (baseCaseUnitary : Unitary 1) 
                -> (1 _ : LVect n Qubit) -> UStateT (t m) (t m) (LVect n Qubit))) ->
  (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQ n m bCU u pat qs = let (qs1 # qs2) = distributeDupedLVect qs in
  applyUST {t=t} qs1 (pat n m u bCU qs2)

||| Using a single recursive layer (like rotate) via PatternQ in QuantumOP  
patternQSingle : UnitaryOp t => QuantumOp t=> (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
  (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQSingle n m bCU u qs = patternQ {t = t} n m bCU u (patternRec) qs

||| Using a double recursive layer (like rotate) via PatternQ in QuantumOP
patternQDouble : UnitaryOp t => QuantumOp t => (n : Nat) -> (m: Nat) -> (baseCaseUnitary : Unitary 1) -> (unitary : (k:Nat) -> Unitary k) -> 
  (1 _ : LVect n Qubit) -> QStateT (t m) (t m) (LVect n Qubit)
patternQDouble n m bCU u qs = patternQ {t = t} n m bCU u (patternRecDouble) qs
