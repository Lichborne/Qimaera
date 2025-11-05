module Main

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import Lemmas
import UnitaryLinear
import QStateT
import UStateT
import UnitarySimulated
import System.Random
import Injection
import QFT
import Grover
import VQE
import Complex
import CoinToss
import QAOA
import Graph
import Examples
import RUS
import Matrix
import UnitarySimulated
import ModularExponentiation
import BinarySimulatedOp
import SimulatedOp
import QuantumOp
import UnitaryNoPrf
import UnitaryNoPrfSim


-- %default total
  

||| Perform 1000 fair coin tosses and count the number of heads
||| (via simulating the quantum dynamics).
testCoins : IO ()
testCoins = do
  let f = coin {t = SimulatedOp}
  s <- sequence (Data.List.replicate 1000 f)
  putStrLn $ "Number of heads: " ++ (show (length (filter (== True) s)))


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


qftTest : (Unitary 4)
qftTest = runUnitaryOp (do
  qs <- supplyQubits 4
  out <- applyUStateT (qftU {i = 4} {n = 4} qs)
  pure out)

qftTestIo : IO ()
qftTestIo = let
  un = qftTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qftTest.py" un
      pure ()  

qftAbsTest : (Unitary 4)
qftAbsTest = runUnitaryOp (do
  qs <- supplyQubits 4
  out <- applyUStateT (qftUAbs {i = 4} {n = 4} qs)
  pure out) 

qftAbsTestIo : IO ()
qftAbsTestIo = let
  un = qftAbsTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qftAbsTest.py" un
      pure () 

qftControlTest : (Unitary 4)
qftControlTest = runUnitaryOp (do
  [c] <- supplyQubits 1
  [q1,q2,q3]<- supplyQubits 3
  out <- applyUStateT ((applyControlledAbs q1 (qftUAbs {i = 3} {n = 3} [c,q2,q3])))
  pure out)

qftControlTestIo : IO ()
qftControlTestIo = let
  un = qftControlTest
  in
    do
      d <- draw un
      eo <- exportToQiskit "qftControlTest.py" un
      pure () 


adderTest : (Unitary 7)
adderTest = runUnitaryOp (do
  a <- supplyQubits 3
  b <- supplyQubits 4
  out <- applyUStateT (inPlaceQFTAdder2 a b)
  pure out)         

adderTestQ : IO (Vect 7 Bool)
adderTestQ = runQ {t = BinarySimulatedOp} (do
               a <- newQubits 3
               b <- newQubits 4 
               outapp <- applyUST (reCombineAbs $ inPlaceQFTAdder a b)
               out <- measureAll (outapp)
               pure out )
         
adderTestIo : IO ()
adderTestIo = let (uni) = adderTest in
    do
      uniq <- adderTestQ
      d2 <- draw uni
      eo <- exportToQiskit "adder.py" uni
      pure ()
     


    
||| testing just the unitary part of modular exponentiation
modularTest : (Unitary 18)
modularTest = runUnitaryOp (do
        c <- supplyQubits 1--- recall that UnitaryOp can only ever get qubits from quantumOp, so we dont have to worry about whether the qubits will be distinct
        ancilla <- supplyQubits 1
        ans <- supplyQubits 3
        xs <- supplyQubits 3
        asnmodinv <- supplyQubits 3
        bigNs <- supplyQubits 3
        nils <- supplyQubits 4
        out <-  applyUStateTSplit (inPlaceModularExponentiation c ancilla (xs) (ans) (asnmodinv) (bigNs) (nils))
        pure out)     
          
modularTestIo : IO (Unitary 18)
modularTestIo = let
  (uni) = modularTest
  (uni1, uni2) = UnitarySimulated.duplicateLinU uni
  in
    do
      d <- draw uni
      eo <- exportToQiskit "modularNewest.py" uni1
      pure uni1 

||| abstract control test; triple control
absControlTestU: UnitaryOp t => (1_ : LVect 5 Qubit) -> UStateT (t 5) (t 5) (LVect 5 Qubit)
absControlTestU [c, c1,c2,q1,q2] =  do
        --(q::qftcs) <- ( (qftUAbs cs))
        --qsq <- reCombine qftcs [q]
        out <- applyControlledAbs c (applyControlledAbs c1 (applyControlledAbs c2 (applyUnitary [q1,q2] (CNOT 0 1 (IdGate {n = 2})))))
        pure (out)

||| run abstract control test
absControlTest : (UnitaryNoPrf 5)
absControlTest = runUnitaryOp (do
        cs <- supplyQubits 5--- recall that UnitaryOp can only ever get qubits from quantumOp, so we dont have to worry about whether the qubits will be distinct
        out <- applyUStateT (absControlTestU cs)
        pure out)   

||| To compare to Unitary n
cccnot : Unitary 5
cccnot = controlled $ controlled $ controlled (CNOT 0 1 (IdGate {n = 2})) --(H 0 (P 0.1 1 (IdGate{n = 4}))) [1,3]

absControlTestIo : IO (UnitaryNoPrf 5)
absControlTestIo = let
  (uni) = absControlTest
  (uni1, uni2) = UnitaryNoPrfSim.duplicateLinU uni
  in
    do
      d <- draw uni2
      eo <- exportToQiskit "absControlTest.py" uni1
      pure uni1

partial public export
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
  --
  --r <- VQE.testVQE
  --putStrLn $ "result from VQE : " ++ show r

  -- QAOA
  putStrLn "\nSmall test with Encoding in VQE"
  --cut <- testQAOA
  --putStrLn $ "result from QAOA : " ++ show cut
  --adder <- adderTestIo
  absControl <- absControlTestIo
  --qftAbs <-qftAbsTestIo
  --qftTest <- qftTestIo
  --qftControl <- qftControlTestIo
  --inPlaceSplitTestC <- inPlaceSplitTestIo
  --modularAdder <- modularAdderTestIo
  --modular <- modularTestIo
  pure ()





