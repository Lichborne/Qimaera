module Examples

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import UnitaryLinear
import QStateT
import UStateT
import System.Random
import Injection
import Complex
import QuantumOp
import UnitarySimulated
import QFT
import ModularExponentiation
import SimulatedOp
import Lemmas


%auto_implicit_depth 50

%search_timeout 1000

------------------------ Example of circuits built with unitary contructors -----------------------

-- These functions only use the 4 constructors of the Unitary data type : IdGate, H, P, and CNOT

||| Put two qubits initally in state |00> in the Bell state; this is the old format, just declaring unitaries
public export
toBellBasis : Unitary 2
toBellBasis = CNOT 0 1 (H 0 IdGate)

||| Draw the circuit toBellBasis using draw function
export
drawToBellBasis : IO ()
drawToBellBasis = do
  putStrLn "\nDrawing ToBellBasis: \nCNOT 0 1 (H 0 IdGate)"
  draw toBellBasis


||| New Format, using Unitary Op.
public export
toBellBasisNew : UnitaryOp t => {n:Nat} -> (1 _ : LVect 2 Qubit) -> UStateT (t (n)) (t (n)) (LVect (2) Qubit)
toBellBasisNew [q0,q1]= do
            [q0] <- applyH q0
            [q0,q1] <- applyCNOT q0 q1
            pure [q0,q1]

||| H 1 (P (pi/2) 2 (CNOT 2 0 IdGate)) - note that because of Idris's current ahndling of Either, 
||| when only using the Unitary type this no longer works automatically, as idris cannot find both whether LT 2 0 or LT 0 2     
constructorsExampleNew : UnitaryOp t => {n:Nat} -> (1 _ : LVect 3 Qubit) -> UStateT (t (n)) (t (n)) (LVect (3) Qubit)
constructorsExampleNew [q1,q2,q3]= do
            [q3n,q1f] <- applyCNOT q3 q1
            [q3f] <- applyP (pi/2) q3n
            [q2f] <- applyH q2
            pure [q1f,q2f,q3f]




---------------------------------- Examples using composition -------------------------------------

-- Sequential composition of unitary circuits
-- Sequential composition in this manner can be used for small things without issue
-- but it is advised that sequential abstract application is used via UnitaryOp 
-- as the more robust equivalent

compose_example1 : Unitary 1
compose_example1 = TGate . HGate

compose_example2 : Unitary 2
compose_example2 = (H 1 IdGate) . (P pi 0 IdGate) . toBellBasis

drawComposeExamples : IO ()
drawComposeExamples = do
  putStrLn "Examples using composition"
  putStrLn "Example 1 : TGate . HGate"
  draw compose_example1
  putStrLn "Example 2 : (H 1 IdGate) . (P pi 0 IdGate) . toBellBasis"
  draw compose_example2

------------------------------------ Examples using tensor product --------------------------------

-- Parallel composition (ie tensor product) of unitary circuits
-- Can still be used, but it is advised that it is used only in the manner below,
-- using the provided gateset or small prebuilts, and once again only as a basis
-- for building larger circuits using UnitaryOp.

||| Example using the # operator for tensor product
tensorExample1 : Unitary 4
tensorExample1 = HGate # PGate pi # CNOTGate

||| Example using tensorn function :
|||Make n tensor products of the same unitary of size 1
tensornExample : Unitary 3
tensornExample = tensorn 3 HGate

||| Example using tensorMapSimple function
||| Tensor product of a Vector of single-qubit Unitary operators
tensorMapSimpleExample : Unitary 3
tensorMapSimpleExample = tensorMapSimple [HGate, PGate pi, HGate]

||| Example using tensorMap function
||| Tensor product of a Vector of Unitary operators
tensorMapExample : Unitary 6
tensorMapExample = tensorMap [CNOTGate, toBellBasis, CNOTGate]

drawTensorExamples : IO ()
drawTensorExamples = do
  putStrLn "Examples using tensor product"
  putStrLn "Example 1 : HGate # PGate pi # CNOTGate"
  draw tensorExample1
  putStrLn "Example 2 : tensorn 3 HGate"
  draw tensornExample
  putStrLn "Example 3 : tensorMapSimple [HGate, PGate pi, HGate]"
  draw tensorMapSimpleExample
  putStrLn "Example 4 : tensorMap [CNOTGate, toBellBasis, CNOTGate]"
  draw tensorMapExample


||| Another version of toBellBasis using composition and tensor product
toBellBasis2 : Unitary 2
toBellBasis2 = CNOTGate . (HGate # IdGate)

drawToBellBasis2 : IO ()
drawToBellBasis2 = do
  putStrLn "\nAnother possibility for toBellBasis: \nCNOTGate . (HGate # IdGate)"
  draw toBellBasis2

---------------------------------------- Examples using adjoint -----------------------------------

-- The adjoint of a unitary circuit is the inverse unitary circuit

adjoint_example1 : Unitary 2
adjoint_example1 = adjoint toBellBasis

adjoint_example2 : Unitary 3
adjoint_example2 = adjoint toffoli

drawAdjointExamples : IO ()
drawAdjointExamples = do
  putStrLn "Examples using adjoint"
  putStrLn "Example 1 : adjoint toBellBasis"
  draw adjoint_example1
  putStrLn "Example 2 : adjoint toffoli"
  draw adjoint_example2


||| Draw an example of circuit using tensor, compose and adjoint
export
exampleComposeTensor1 : IO ()
exampleComposeTensor1 = do
  putStrLn "\nAn example of usage of compose, tensor and adjoint: \n(adjoint toBellBasis # IdGate) . (TGate # toBellBasis)"
  let circuit = (adjoint toBellBasis # IdGate) . (TGate # toBellBasis)
  draw circuit


---------------------------------------- Examples using apply -------------------------------------

-- Apply : apply a smaller unitary circuit of size i to a bigger one of size n, giving the vector v of wire indices on which we wish to apply the smaller circuit

U : Unitary 3
U = HGate # IdGate {n = 1} # (PGate pi)

apply_example1 : Unitary 3
apply_example1 = apply toBellBasis U [0,1]

apply_example2 : Unitary 3
apply_example2 = apply toBellBasis U [0,2]

-------------------------------------- Example using controlled -----------------------------------

-- Compute the controlled version of a unitary circuit

controlled_example1 : Unitary 2
controlled_example1 = controlled TGate

||| Example using multipleQubitControlledNOT
||| Makes a multiple qubit CNOT gate : control on the first n qubits, target on the last
multipleQubitsCNOTExample : Unitary 4
multipleQubitsCNOTExample = multipleQubitControlledNOT 4

--------------------------------- Examples of parametrized circuits -------------------------------

-- Unitary circuits can be parametrized by classical information


parametrized_example1 : Bool -> Unitary 1
parametrized_example1 b = if b then HGate else PGate pi

parametrized_example2 : Bool -> Bool -> Double -> Unitary 2
parametrized_example2 b1 b2 p = CNOTGate . (if b1 then H 0 IdGate else IdGate) . (if b2 then IdGate else P p 1 IdGate)

drawParamExamples : IO ()
drawParamExamples = do
  putStrLn "Examples of circuits parametrized by classical data"
  putStrLn "Example 1 : for b : bool , if b then HGate else PGate pi"
  putStrLn "For b = True : "
  draw (parametrized_example1 True)
  putStrLn "For b = False : "
  draw (parametrized_example1 False)
  putStrLn "Example 2 : for b1, b2 : Bool and p : Double , CNOTGate . (if b1 then H 0 IdGate else IdGate) . (if b2 then IdGate else P p 1 IdGate)"
  putStrLn "For b1 = True, b2 = False, p = pi/2"
  draw (parametrized_example2 True False (pi/2))


------------------------------------ Example of depth computation ---------------------------------
-- Compute the depth of a circuit 


depthExample2 : Unitary 3
depthExample2 = H 2 $ H 1 $ H 0 $ H 1 IdGate

depthExample3 : Unitary 3
depthExample3 = CNOT 1 2 $ CNOT 2 0 $ CNOT 0 1 $ H 1 $ P pi 1 $ H 1 IdGate

drawDepthExamples : IO ()
drawDepthExamples = do
  putStrLn "Examples of depth computation"
  putStrLn "\n\nThe depth of the following circuit"
  draw depthExample2
  putStrLn $ "is " ++ show (depth depthExample2)
  putStrLn "\n\nThe depth of the following circuit"
  draw depthExample3
  putStrLn $ "is " ++ show (depth depthExample3)


----------------------------------- Examples of quantum operations --------------------------------

||| Sequencing quantum operations using run
||| 
quantum_operation4 : UnitaryOp t => QuantumOp t => QStateT (t 0) (t 0) (Vect 3 Bool)
quantum_operation4 = do
      [q1,q2] <- newQubits {t=t} 2                      --create 2 new qubits q1 and q2
      [q1,q2] <- applyUST (toBellBasisNew [q1,q2])       --apply the toBellBasis unitary circuit to q1 and q2
      q3 <- newQubit {t = t}                                     --create 1 new qubit q3
      [q1,q3,q2] <- applyUST (applyUnitary [q1,q3,q2] toffoli)     --apply toffoli gate on q1, q3 and q2
      [b2] <- measure {t = t} [q2]                              --measure q2
      [q3,q1] <- applyUST (applyCNOT q3 q1)                     --apply CNOT on q3 and q1
      [b1,b3] <- measure {t = t} [q1,q3]                        --measure q1 and q3
      pure [b1,b2,b3]                                   --return the results
  
runQuantumOp4 : UnitaryOp t => QuantumOp t => IO (Vect 3 Bool)  
runQuantumOp4 = runQ {t=t} (do
          bs <- quantum_operation4 {t = t}
          pure bs)

testQuantumOp4 : IO (Vect 3 Bool) 
testQuantumOp4 = do
      bs <- runQuantumOp4 { t = SimulatedOp }
      pure bs         

drawQuantumOp : IO () 
drawQuantumOp = do
      [b1,b2,b3] <- testQuantumOp4
      putStrLn "\n\nExecuting an example of quantum operations : sequencing quantum operations using run"
      putStrLn "Create 2 qubits q1 and q2"
      putStrLn "Apply `toBellBasis` circuit on q1 and q2"
      putStrLn "Create one new qubit q3"
      putStrLn "Apply the toffoli gate on q1,q3 and q2"
      putStrLn $ "Measure q2 : result is " ++ show b2
      putStrLn $ "Measure q1 and q3 : results are " ++ show b1 ++ " and " ++ show b3

-------------------------- Various Tests for Split Computation -------------------------
inPlaceSplitTest : UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (3 + i)  Qubit) (LVect ((S i)) Qubit)) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceSplitTest [c1,c2] [ancilla] [] [q] = pure $ (c1::c2::[ancilla]) # [q]
inPlaceSplitTest [c1,c2] [ancilla] bigNs (b::bs) = do
    bs <- (qftUInv (b::bs)) 
    (bigNs) # bs <-(inPlaceQFTAdder bigNs (bs))
    bs <- (qftU (bs)) -- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    pure $ ((++) (c1::c2::[ancilla]) bigNs) # (bs)

export
inPlaceSplitTestC : UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LVect ((3 + i) + (S i)) Qubit) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceSplitTestC [c1,c2] [ancilla] [] [q] = pure $ (c1::c2::ancilla::[q])
inPlaceSplitTestC {i = S k} [c1,c2] [ancilla] bigNs (b::bs) = do
    bs <- (qftUInv (b::bs)) 
    (c2::bigNsbs) <- applyControlledAbs c2 (inPlaceQFTAdder2 bigNs (bs))
    bigNs2 # bs2 <- splitQubitsInto (S k) (S (S k)) bigNsbs
    bs <- (qftU (bs2)) -- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    rest <- reCombine (c1::c2::[ancilla]) bigNs2
    pure $ ((++) rest bs)

||| Test of split control with second control qubit
inPlaceSplitTestCS : UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (3 + i)  Qubit) (LVect ((S i)) Qubit)) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceSplitTestCS [c1,c2] [ancilla] [] [q] = pure $ (c1::c2::[ancilla]) # [q]
inPlaceSplitTestCS [c1,c2] [ancilla] bigNs (b::bs) = do
    bs <- (qftUInv (b::bs)) 
    (c2::bigNs) # bs <-applyControlWithSplitLVects c2 (inPlaceQFTAdder bigNs (bs))
    bs <- (qftU (bs)) -- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    pure $ ((++) (c1::c2::[ancilla]) bigNs) # (bs)

||| Run 
inPlaceSplitTestU : (Unitary 8)
inPlaceSplitTestU = runUnitaryOp (do
        cs <- supplyQubits 2--- recall that UnitaryOp can only ever get qubits from quantumOp, so we dont have to worry about whether the qubits will be distinct
        ancilla <- supplyQubits 1
        bigN <- supplyQubits 2
        b <- supplyQubits 3
        out <-  applyUStateTSplit (inPlaceSplitTestCS cs ancilla (bigN) (b))
        pure out)   

inPlaceSplitTestIo : IO (Unitary 8)
inPlaceSplitTestIo = let
  (uni) = inPlaceSplitTestU
  (uni1, uni2) = UnitarySimulated.duplicateLinU uni
  in
    do
      d <- draw uni
      eo <- exportToQiskit "splittest.py" uni1
      pure uni1 

------------------------------------ Draw all example circuits ------------------------------------

export
drawExamples : IO ()
drawExamples = do
  drawComposeExamples
  drawTensorExamples
  drawToBellBasis2
  drawAdjointExamples
  exampleComposeTensor1
  drawParamExamples
  drawDepthExamples
