module Main

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import Qubit
import Lemmas
import UnitaryLinear
import UnitaryNoPrf
import QStateT
import UStateT
import UnitaryOp
import UnitarySimulated
import System.Random
import Injection
import QFT
import Grover
import VQE
import Complex
import QuantumOp
import CoinToss
import QAOA
import Graph
import Examples
import RUS
import Matrix
import UnitarySimulated
import UnitaryNoPrfSim
import ModularExponentiation
import SimulatedCircuit



-- %default total
  

||| Perform 1000 fair coin tosses and count the number of heads
||| (via simulating the quantum dynamics).
testCoins : IO ()
testCoins = do
  let f = coin {t = SimulatedOp}
  s <- sequence (Data.List.replicate 1000 f)
  let heads = filter (== True) s
  putStrLn $ "Number of heads: " ++ (show (length heads))


||| Test graph for the QAOA problem
export
graph1 : Graph 5
graph1 = AddVertex (AddVertex (AddVertex (AddVertex (AddVertex Empty []) [True]) [True, True]) [False, True, False]) [False, False, True, True]

||| Execute QAOA with 100 samples on the previous graph to solve the MAXCUT problem
export
testQAOA : IO (Cut 5)
testQAOA = do
  QAOA {t = SimulatedOp} 100 1 graph1


||| Small test for the VQE algorithm
export
testVQE : IO Double
testVQE = do
  putStrLn "Test VQE"
  let hamiltonian = [(2, [PauliX, PauliY]),(3,[PauliZ, PauliI])]
  VQE {t = SimulatedOp} 2 hamiltonian 5 10 5


||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))


||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)
||| Auxiliary function for QFT : builds the recursive pattern
|||
||| n -- number of qubits
export
qftRec : (n : Nat) -> Unitary n
qftRec 0 = IdGate
qftRec 1 = HGate
qftRec (S (S k)) =   let t1 = (qftRec (S k)) # IdGate
  in rewrite sym $ lemmaplusOneRight k in apply (Main.cRm (S (S k))) t1 [S k, 0] 

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

qftAbsTest : LPair (Unitary 4) (LVect 4 Qubit)
qftAbsTest = let 
    a = (MkQubit 0 :: MkQubit 1 :: MkQubit 2 :: [MkQubit 3])
    in runUnitarySim (IdGate {n  = 4}) (do
            out <- qftUAbs {i = 4} {n = 4} (toLVectQQ a)
            pure out)

qftAbsTestIo : IO ()
qftAbsTestIo = let
  un # lvect = qftAbsTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qftAbs.py" un
      pure () 

qftTest : LPair (Unitary 4) (LVect 4 Qubit)
qftTest = let 
    a = (MkQubit 0 :: MkQubit 1 :: MkQubit 2 :: [MkQubit 3])
    in runUnitarySim (IdGate {n  = 4}) (do
            out <- qftU (toLVectQQ a)
            pure out)
            
qftTestIo : IO ()
qftTestIo = let
  un # lvect = qftTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qft.py" un
      eo <- exportToQiskit "ogqft.py" (qft 4)
      pure () 
    
{-}
qftAbsTest : LPair (SimulatedOp 4) (LVect 4 Qubit)
qftAbsTest = let 
    a = (MkQubit 0 :: MkQubit 1 :: MkQubit 2 :: [MkQubit 3])
    in run' (MkSimulatedOp {n = 4} (neutralIdPow 4) IdGate a 4 ) (do
            out <- qftUAbs {i = 4} {n = 4} (toLVectQQ a)
            pure out)

qftAbsTestIo : IO ()
qftAbsTestIo = let
  (MkSimulatedOp qs un vect counter) # lvect = qftAbsTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qftAbs.py" un
      pure () 

qftTest : LPair (SimulatedOp 4) (LVect 4 Qubit)
qftTest = let 
    a = (MkQubit 0 :: MkQubit 1 :: MkQubit 2 :: [MkQubit 3])
    in run' (MkSimulatedOp (neutralIdPow 4) IdGate a 4 {n=4}) (do
            out <- qftU (toLVectQQ a)
            pure out)
            
qftTestIo : IO ()
qftTestIo = let
  (MkSimulatedOp qs un vect counter) # lvect = qftTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qft.py" un
      eo <- exportToQiskit "ogqft.py" (qft 4)
      pure () 
    -}

adderTest : LPair (UnitaryNoPrf 3) (LVect 7 Qubit)
adderTest = let 
        a = (MkQubit 0 :: MkQubit 1 ::[MkQubit 2])
        b = (MkQubit 3 :: MkQubit 4  :: MkQubit 5 :: [MkQubit 6])
        in 
          runUnitaryNoPrfSim (IdGate {n=3}) (do
            out <- inPlaceQFTAdder2 a b
            pure out)         

adderTestQ : IO (Vect 7 Bool)
adderTestQ = runQ {t = SimulatedCircuit} (do
               a <- newQubits 3
               b <- newQubits 4 
               outapp <- applyUnitaryQ (reCombineAbs $ inPlaceQFTAdder a b)
               out <- measureAll (outapp)
               pure out )
            
adderTestIo : IO ()
adderTestIo = do
  any <- adderTestQ
  pure ()
{- let
  (uni) # lvect = adderTest
  in
    do
      d <- draw uni
      eo <- exportToQiskit "adder.py" uni
    pure () -}
      

encodingTest : LPair (Unitary 5) (LVect (5) Qubit)
encodingTest = let 
        p = [PauliX, PauliY, PauliZ, PauliI]
        qs = (MkQubit 0 :: MkQubit 1 :: MkQubit 2 :: MkQubit 3 :: [MkQubit 4])
        in 
          runUnitarySim (IdGate {n=5}) (do
            out <- encodingUnitaryOp p qs
            pure out)

encodingTestU : Unitary 5
encodingTestU = let 
        p = [PauliX, PauliY, PauliZ, PauliI]
        in 
        encodingUnitary p 

encodingTestIo : IO ()
encodingTestIo = let
  uni # lvect = encodingTest
  in
    do
      eo <- exportToQiskit "encoding.py" uni
      d <- draw uni
      d2 <- draw encodingTestU
      pure () 

mkQubitList : (from:Nat) -> (i:Nat) -> LVect i Qubit
mkQubitList Z Z = []
mkQubitList (S k) Z = []
mkQubitList Z (S k) = (MkQubit Z :: mkQubitList (S Z) k)     
mkQubitList (S n) (S k) = (MkQubit (S n) :: mkQubitList (S (S n)) k)   

||| testing just the unitary part of modular exponentiation
modularTest : LPair (UnitaryNoPrf 5) (LPair (LVect (3 + 3 + 3 + 3 + 3) Qubit) (LVect (3) Qubit))
modularTest = let 
        c = [MkQubit 0] --- recall that UnitaryOp can only ever get qubits from quantumOp, so we dont have to worry about whether the qubits will be distinct
        ancilla = [MkQubit 1]
        ans = mkQubitList 2 3
        xs = mkQubitList 5 3
        asnmodinv = mkQubitList 8 3
        bigNs = mkQubitList  11 3
        nils = mkQubitList 14 4
        in 
          runSplitUnitaryNoPrfSim (IdGate {n=5}) (do
            out <-  inPlaceModularExponentiation c ancilla (xs) (ans) (asnmodinv) (bigNs) (nils)
            pure out)     
          
modularTestIo : IO ()
modularTestIo = let
  (uni) # lvect = modularTest
  in
    do
      d <- draw uni
      eo <- exportToQiskit "modular.py" uni
      pure () 
    {-}
modularTest : LPair (Unitary 5) (LPair (LVect (3 + 5 + 5 + 5 + 5) Qubit) (LVect (5) Qubit))
modularTest = let 
        c = [MkQubit 0] --- recall that UnitaryOp can only ever get qubits from quantumOp, so we dont have to worry about whether the qubits will be distinct
        ancilla = [MkQubit 1]
        ans = (MkQubit 2 :: MkQubit 3 :: MkQubit 4 :: MkQubit 5 :: [MkQubit 6])
        xs = (MkQubit 7 :: MkQubit 8 :: MkQubit 9 :: MkQubit 10 :: [MkQubit 11])
        asnmodinv = (MkQubit 12 :: MkQubit 13 :: MkQubit  14 :: MkQubit 15 :: [MkQubit 16])
        bigNs = (MkQubit 17 :: MkQubit 18 :: MkQubit 19 :: MkQubit 20 :: [MkQubit 21])
        nils = (MkQubit 22 :: MkQubit 23 :: MkQubit 24 :: MkQubit 25 :: MkQubit 26 :: [MkQubit 27])
        in 
          runSplitUnitarySim (IdGate {n=5}) (do
            out <-  inPlaceModularExponentiation c ancilla (xs) (ans) (asnmodinv) (bigNs) (nils)
            pure out)     

modularTestIo : IO ()
modularTestIo = let
  uni # lvect = modularTest
  in
    do
      d <- draw uni
      eo <- exportToQiskit "modular.py" uni
      pure () 
    -}


public export
main : IO ()
main = do

  -- Execute the example file and draw the circuit examples
  drawExamples

  -- Draw the Quantum Fourier Transform for n = 3
  --  putStrLn "\n\n\nQuantum Fourier Transform for n = 3"
  --  draw (qft 3)


  -- Execute the coin toss example
  putStrLn "\nTest coin toss by performing 1000 coin tosses."
  testCoins

  -- Repeat until success
  putStrLn "\nTest 'Repeat Until Success'. Probability to measure '1' is 2/3 for this example."
  --b <- testMultipleRUS 3

  -- VQE
  putStrLn "\nSmall test with VQE"
  --r <- VQE.testVQE
  --putStrLn $ "result from VQE : " ++ show r

  -- QAOA
  putStrLn "\nSmall test with Encoding in VQE"
  cut <- testQAOA
  putStrLn $ "result from QAOA : " ++ show cut
  --k <- encodingTestIo
  ast <- adderTestIo
  abs <-qftAbsTestIo
  normie <- qftTestIo
  normie <- qftAbsTestIo
  --modular <- modularTestIo
  pure ()





