module BinarySimulatedOp

import Data.Vect
import Data.Vect.Sort
import Data.Nat
import Data.Nat.Views
import Decidable.Equality
import System.File
import Injection
import System.Random
import Lemmas
import QStateT
import LinearTypes
import UnitaryLinear
--import UnitaryOp
import UStateT
import Control.Linear.LIO
import QuantumOp

public export
data BinarySimulatedOp : Nat -> Type where
  MkBinarySimulatedOp : {n : Nat} -> Unitary n -> Vect n Qubit -> Nat -> String ->  BinarySimulatedOp n
  

||| New qubits in BinarySimulatedOp
newQubitsSimulatedCirc : (p : Nat) -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulatedCirc p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : BinarySimulatedOp m) -> R (LPair (BinarySimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkBinarySimulatedOp un v counter str) =
    let (qubits # (v', newcounter)) = newQubitsPointers q counter v
    in pure1 (MkBinarySimulatedOp ( un # IdGate ) (v ++ v') (newcounter) str # qubits)


||| Helper for BinarySimulatedOp implementatstrn of abstract unitary applicatstrn (that is, whatever one built using UStateT)
applyUnitaryCirc': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUnitaryCirc' ust (MkBinarySimulatedOp un v counter str) = 
  let ((MkBinarySimulatedOp unew vnew vacuousCounter str) # lvect) = runUStateT (MkBinarySimulatedOp un v counter str) ust in
        let unew = compose unew un in
          do pure1 ((MkBinarySimulatedOp unew vnew counter str) # (lvect))

||| BinarySimulatedOp implementatstrn of abstract unitary applicatstrn (that is, whatever one built using UStateT)
applyUnitaryCircSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i  Qubit)
applyUnitaryCircSimulated ust = MkQST (applyUnitaryCirc' ust )

||| Helper for BinarySimulatedOp implementatstrn of abstract unitary applicatstrn (that is, whatever one built using UStateT)
applyUDirectlyCirc': {n : Nat} -> {i : Nat} -> (Unitary i) -> (1_ : LVect i Qubit)
                   -> (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUDirectlyCirc' ui li (MkBinarySimulatedOp un v counter str) = 
      let lvect # vect = distributeDupedLVectVect li in
        let unew = apply ui un vect in
          do pure1 ((MkBinarySimulatedOp unew v counter str) # (lvect))

||| BinarySimulatedOp implementatstrn of abstract unitary applicatstrn (that is, whatever one built using UStateT)
applyUDirectlyCircSimulated : {n : Nat} -> {i : Nat} -> (Unitary i) -> (1_ : LVect i Qubit)      
                   -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)
applyUDirectlyCircSimulated ui li = MkQST (applyUDirectlyCirc' ui li)


||| Utility for adding a string to a the string obtained from a unitary
addString : {n : Nat} -> String -> Unitary n -> String
addString str g =
  let s = unitarytoQiskit g in
  (str ++ s)

||| Measurement for a simulated circuit; this is randomized 50%-50%;
||| This is precisely the intention of this implementation, to get the circuits produced
||| by algorithms, including variational ones, depending on measurement outcomes, randomly
private
measureCirc' : {n : Nat} -> (i : Nat) ->
           (1 _ : BinarySimulatedOp (S n)) ->
           R (LFstPair (BinarySimulatedOp n) (Bool))
measureCirc' {n} i (MkBinarySimulatedOp usn w counter str) = do
  let newQubits = removeElem w i
  randnb <- liftIO1 (rndFin 1)
  case randnb of 
     0 => do
       pure1 (MkBinarySimulatedOp IdGate newQubits i (addString str usn) # (False))
     1 => do
       pure1 (MkBinarySimulatedOp IdGate newQubits i (addString str usn) # (True))


||| Relevant version of list index       
public export
listIndexCirc : (1 _ : BinarySimulatedOp n) -> (1 _ : Qubit) -> LFstPair (LPair (BinarySimulatedOp n) Qubit) Nat
listIndexCirc (MkBinarySimulatedOp us v counter str ) q = let (q, k) = qubitToNatPair q in (MkBinarySimulatedOp us v counter str # q) # (listIndex' v q)

private
measureQubitsCirc' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : BinarySimulatedOp (i + n)) -> R (LPair (BinarySimulatedOp n) ((Vect i Bool)))
measureQubitsCirc' [] qs = pure1 (qs # [])
measureQubitsCirc' (x :: xs) (MkBinarySimulatedOp uin v counter str) = 
  let (qs' # q) # y = listIndexCirc (MkBinarySimulatedOp uin v counter str) x in
    let (q, k) = qubitToNatPair q in 
      do  
        (s # (b)) <- measureCirc' y qs'
        (s1 # (bs)) <- measureQubitsCirc' xs s
        case bs of 
            [] => pure1 (s1 # ([b]))
            (b' :: bs') => pure1 (s1 # ((b :: b' :: bs')))

||| Measure some qubits in a quantum state
export
measureSimulatedCirc : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (BinarySimulatedOp (i + n)) (BinarySimulatedOp n) (Vect i Bool)
measureSimulatedCirc v = MkQST (measureQubitsCirc' v)

||| The beginning of output files; the circuit size may or may not be correct! depends on whether we measured all qubits or not.
baseString : (n:Nat) -> String
baseString n = ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show n ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n")

runSimulatedCirc : {n:Nat} -> QStateT (BinarySimulatedOp 0) (BinarySimulatedOp 0) (Vect n Bool) -> IO (Vect n Bool)
runSimulatedCirc {n} s = LIO.run (do
  ((MkBinarySimulatedOp un w c str) # v) <- runQStateT (MkBinarySimulatedOp IdGate [] 0 (baseString n)) s
  nothing <- putStrLn "Please give a name to the file you wish to export the circuit to:  "
  name <- getLine
  uinout <- writeFile (name ++ ".py") (str ++ "\nprint(qc)")
  case v of 
                    [] => pure []
                    (x :: xs) => pure (x :: xs))
  

||| Implementatstrn of run for BinarySimulatedOp
public export
runSimulatedCircU : {i:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit) ) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
runSimulatedCircU {i = i} simop ust = runUStateT simop ust

public export
exportUnitary' : {i:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit) ) -> Unitary n
exportUnitary' {i = i} simop ust = let (MkBinarySimulatedOp un vn counter str) # lvect = runUStateT simop ust in
                                      let () = discardq lvect in
                                          un

||| Implementatstrn of runSplit BinarySimulatedOp
public export
runSplitSimulatedCircU : {i:Nat} -> {j:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitSimulatedCircU {i = i} simop ust = runUStateT simop ust

||| Helper for implementatstrn of  applyUnitary
applyUnitarySimulatedCirc' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( MkUnitary (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUnitarySimulatedCirc' lvIn ui (MkBinarySimulatedOp un v counter str)= let lvOut # vect = distributeDupedLVectVect lvIn in 
  (MkBinarySimulatedOp ((apply ( ui) un vect)) v counter str) # lvOut

||| BinarySimulatedOp implementatstrn of applyUnitary
export
applyUnitarySimulatedCirc : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> Unitary i -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)
applyUnitarySimulatedCirc lvect ui = MkUST (applyUnitarySimulatedCirc' lvect (ui))

||| Helper for BinarySimulatedOp implementatstrn of applyUnitaryOwn (using self-defined datatype for unitaries)
private
applyUnitaryOwnCirc' : {n : Nat} -> {i : Nat} -> (1 _ : BinarySimulatedOp i) -> (1 _ : LVect i Qubit) ->
   (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUnitaryOwnCirc' {n} {i} (MkBinarySimulatedOp uis vacuousV vacuousC vacuousStr) lvIn (MkBinarySimulatedOp un v counter str) = 
    let lvOut # vect = distributeDupedLVectVect lvIn in 
      let unew = apply uis un (vect) in
        do ((MkBinarySimulatedOp unew v counter str) # (lvOut))

||| BinarySimulatedOp implementatstrn of applyUnitaryOwn (using self-defined datatype for unitaries)
export
applyUnitaryOwnSimulatedCirc : {n : Nat} -> {i : Nat} -> (1 _ :LVect i Qubit) -> 
  (1 _ : BinarySimulatedOp i) -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)
applyUnitaryOwnSimulatedCirc {n} {i} qbits simop = MkUST (applyUnitaryOwnCirc' {n =n} {i = i} simop qbits)


||| Helper for BinarySimulatedOp implementatstrn of abstract unitary applicatstrn (that is, whatever one built using UStateT)
applyUnitaryAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
applyUnitaryAbs' ust (MkBinarySimulatedOp un v counter str) = 
  let (MkBinarySimulatedOp unew vnew vacuousCounter vacuousStr # lvect) = runUStateT (MkBinarySimulatedOp un v counter str) ust in
        let unew = compose unew un in
          do ((MkBinarySimulatedOp unew vnew counter str) # (lvect))

||| BinarySimulatedOp implementatstrn of abstract unitary applicatstrn (that is, whatever one built using UStateT)
applyUnitaryAbsSimulatedCirc : {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i  Qubit)
applyUnitaryAbsSimulatedCirc ust = MkUST (applyUnitaryAbs' ust )


||| Auxiliary functstrn for applying a circuit to some qubits
private
reCombineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect (i +j) Qubit))
reCombineAbs' ust (MkBinarySimulatedOp us v counter str) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitSimulatedCircU (MkBinarySimulatedOp us v counter str) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))
 
export
reCombineAbsSimulatedCirc : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (i+j) Qubit)
reCombineAbsSimulatedCirc q = MkUST (reCombineAbs' q)

--(1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair Qubit (LVect i Qubit))) ->

||| One must be extremelhy careful with the targets here because there are no guarantees if one wishes to do this!
private
applyControlOnly' : {n : Nat} -> {i : Nat} -> (1 _ : BinarySimulatedOp i) -> (1 _ : Qubit) -> 
   (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect (S i) Qubit))
applyControlOnly' {n} {i} (MkBinarySimulatedOp uis vi vacuousC vacuousStr) q (MkBinarySimulatedOp un v counter str) = 
   let (q, k) = qubitToNatPair q in
      let unew = apply (controlled uis) un ((k:: (toVectN vi))) in
        do ((MkBinarySimulatedOp unew v counter str) # (q :: toLVectQQ vi))

--(1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair Qubit (LVect i Qubit))) ->
export
applyControlOnlySimulated : {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 _ : BinarySimulatedOp i) ->      
    UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (S i) Qubit)
applyControlOnlySimulated control simop = MkUST (applyControlOnly' simop control)

private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))->      
    (1_ : BinarySimulatedOp (S n)) -> LPair (BinarySimulatedOp (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} q ust (MkBinarySimulatedOp usn vsn csn str)= 
  let (q, k) = qubitToNatPair q in
    let vn = findInLinQ q vsn in
      let (MkBinarySimulatedOp un vn dummyc summystr) # lvOut = runUStateT (MkBinarySimulatedOp  (IdGate {n = n}) vn n str) ust in
        let unew = apply (controlled un) usn (k :: (toVectN vn)) in
          (MkBinarySimulatedOp unew vsn csn str) # (q :: lvOut)

export
applyControlAbsSimulatedCirc: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))->      
    UStateT (BinarySimulatedOp (S n)) (BinarySimulatedOp (S n)) (LVect (S i) Qubit)
applyControlAbsSimulatedCirc ctrl ust = MkUST (applyControlSimulated' ctrl ust)   

invertBinarySimulatedOp : (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)) -> (1_ : (BinarySimulatedOp n)) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
invertBinarySimulatedOp ust (MkBinarySimulatedOp u v counter str)=  
    let (MkBinarySimulatedOp un vn counter str) # lvOut = runUStateT (MkBinarySimulatedOp (IdGate {n = n}) v counter str) ust in
        let invu = adjoint un in
          let unew = compose invu u in
              (MkBinarySimulatedOp unew v counter str) # (lvOut)
export
adjointUSTSimCirc' : (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)) -> (UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))
adjointUSTSimCirc' ust = MkUST (invertBinarySimulatedOp ust)


applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (MkBinarySimulatedOp un v counter str) = 
  let ((MkBinarySimulatedOp unew vnew vacuousCounter vacuousStr) # lvect) = runUStateT (MkBinarySimulatedOp un v counter str) ust in
        let unew = compose unew un in
          do ((MkBinarySimulatedOp unew vnew counter str) # (lvect))

||| Implementatstrn of abstract split applicatstrn - representatstrnally useful
applyWithSplitLVectsSimulatedCirc : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulatedCirc ust = MkUST (applyWithSplitLVects' ust)

||| Helper for implementatstrn of abstract controlled split applicatstrn 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> (1_ : BinarySimulatedOp (S n)) -> LPair (BinarySimulatedOp (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' q ust (MkBinarySimulatedOp usn vsn csn str)= 
  let (q, k) = qubitToNatPair q in
    let vn = findInLinQ q vsn in
      let (MkBinarySimulatedOp un vn dummyc dummystr) # (lvLeft # lvRight)= runUStateT (MkBinarySimulatedOp  (IdGate {n = n}) vn n str) ust in
        let unew = apply (controlled un) usn (k :: (toVectN vn)) in
          (MkBinarySimulatedOp unew vsn csn str) # ((q :: lvLeft) # lvRight)

||| Implementatstrn of abstract controlled split applicatstrn     
applyControlledSimulatedSplitCirc: {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> UStateT (BinarySimulatedOp (S n)) (BinarySimulatedOp (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledSimulatedSplitCirc ctrl ust = MkUST (applyControlledUSplitSim' ctrl ust)   


applyParallelSimulatedBinary': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))     
                   -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect j Qubit))   
                   -> (1 _ : BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect (i + j) Qubit)
applyParallelSimulatedBinary' ust1 ust2 (MkBinarySimulatedOp un vn cn st) = 
  let ((MkBinarySimulatedOp unew1 vnew1 vacnew1 vacstr1) # lvecti) = runUStateT (MkBinarySimulatedOp IdGate vn cn st) ust1 in -- there are multiple choices for what order to do what in, this is one correct one
    let ((MkBinarySimulatedOp unew2 vnew2 vacnew2 vacstr2) # lvectj) = runUStateT (MkBinarySimulatedOp IdGate vn cn st) ust2 in
        let unewest = compose unew1 un in
          let uOut = compose unew2 unewest in
            do ((MkBinarySimulatedOp uOut vnew2 cn st) # (lvecti ++ lvectj))

export
applyParallelSimulatedBinary: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) ((LVect i Qubit)))
                        -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) ((LVect j Qubit))) -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (i + j) Qubit)
applyParallelSimulatedBinary ust1 ust2 = MkUST (applyParallelSimulatedBinary' ust1 ust2)

export
UnitaryOp BinarySimulatedOp where
  applyUnitary = applyUnitarySimulatedCirc
  applyUnitaryOwn = applyUnitaryOwnSimulatedCirc
  --applyUnitaryAbs = applyUnitaryAbsSimulatedCirc
  applyControlledAbs = applyControlAbsSimulatedCirc
  adjointUST = adjointUSTSimCirc'
  applyParallel = applyParallelSimulatedBinary
  --applyControlWithSplitLVects = applyControlledSimulatedSplitCirc
  ----applyWithSplitLVects = applyWithSplitLVectsSimulatedCirc
  --reCombineAbs= reCombineAbsSimulatedCirc
  run          = runSimulatedCircU
  --runSplit = runSplitSimulatedCircU

export
QuantumOp BinarySimulatedOp where
  newQubits    = newQubitsSimulatedCirc
  applyUST = applyUnitaryCircSimulated
  applyUnitaryDirectly = applyUDirectlyCircSimulated
  measure      = measureSimulatedCirc
  runQ          = runSimulatedCirc