module Main

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import Lemmas
import UnitaryLinear
import UnitaryNoPrf
import QStateT
import UStateT
--import UnitaryOp
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
import UnitaryNoPrfSim
import ModularExponentiation
import BinarySimulatedOp
import SimulatedOp
import QuantumOp


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
  in rewrite sym $ lemmaplusOneRight k in 
    let u # _ = applyOrErrorIO (Main.cRm (S (S k))) t1 [S k, 0] in
      u

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
      eo <- exportToQiskit "qftAbs.py" un
      pure () 
{-}
qftTest : (m: Nat) -> (Unitary m)
qftTest m = let 
    a # _ = newQubitsPointersNoCount m []
    in exportSelf (IdGate {n  = m}) (qftU a)
            
qftTestIo : IO ()
qftTestIo = let
  un = qftTest 4
  in
    do
      d <- draw un
      eo <- exportToQiskit "qftinv.py" un
      --eo <- exportToQiskit "ogqft.py" (qft 4)
      pure () 
    
b: LVect 4 Qubit
b = let a # av = newQubitsPointersNoCount 3 [] in
    let b # _ = newQubitsPointersNoCount 4 av in b
-}
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
      d <- draw uni
      eo <- exportToQiskit "adderNew.py" uni
      pure ()
     
{-}
encodingTest : LPair (Unitary 5) (LVect (5) Qubit)
encodingTest = let 
        p = [PauliX, PauliY, PauliZ, PauliI]
        qs = mkQubitList 0 5
        in 
          runUnitarySim (IdGate {n=5}) (do
            out <- encodingUnitaryOp p qs
            pure out)

encodingTestU : Unitary 5
encodingTestU = let 
        p = [PauliX, PauliY, PauliZ, PauliI]
        in 
        encodingUnitary p 

encodingTest : LPair (Unitary 3) (LVect (3) Qubit)
encodingTest = let 
        p = [PauliZ, PauliI]
        qs # _ = newQubitsPointersNoCount 3 []
        in 
          runUnitarySim (IdGate {n=3}) (do
            out <- encodingUnitaryOp p qs
            pure out)

encodingTestU : Unitary 3
encodingTestU = let 
        p = [PauliZ, PauliI]
        in 
        encodingUnitary p 

encodingTestIo : IO ()
encodingTestIo = let
  uni # lvect = encodingTest
  in
    do
      eo <- exportToQiskit "encodingstupid.py" uni
      d <- draw uni
      d2 <- draw encodingTestU
      pure () 
-}


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
  --k <- encodingTestIo
  --ast <- adderTestIo
  --abs <-qftAbsTestIo
  --normie <- qftTestIo
  normie <- qftAbsTestIo
  --modular <- modularTestIo
  --qftabs <- testQFTAbs12
  pure ()





