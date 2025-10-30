module UnitarySimulated

import Data.Vect
import Data.Nat
import Control.Monad.State
import Decidable.Equality
import System.File
import Injection
import Matrix
import SimulatedOp
import Complex
import Lemmas
import UnitaryLinear
import UStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Data.Maybe
import QStateT
import Data.Linear.Notation
import Data.Linear.Interface
import QuantumOp



public export
runUnitarySim : {i:Nat} -> (1_: Unitary n) -> (1 _ : UStateT (Unitary n) (Unitary n) (LVect i Qubit) ) -> LPair (Unitary n) (LVect i Qubit)
runUnitarySim {i = i} un ust = runUStateT un ust

public export
runSplitUnitarySim : {i:Nat} -> {j:Nat} -> (1_: Unitary n) -> (1 _ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitUnitarySim {i = i} un ust = runUStateT un ust

public export
exportUnitarySelf : {i:Nat} -> (1_: Unitary n) -> (1 _ : UStateT (Unitary n) (Unitary n) (LVect i Qubit) ) -> (Unitary n) 
exportUnitarySelf un ust = let op # lvect = runUStateT un ust in
                                      let () = discardq lvect in
                                        op
||| Auxiliary function for applying a circuit to some qubits
private
applyUnitary' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect i Qubit))
applyUnitary' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
                          let un # _ = ( (applyOrErrorIO ui u vect) ) in un # lvOut

export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect (ui))

private
applyUnitaryOwn' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> (1_ : Unitary i) -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect i Qubit))
applyUnitaryOwn' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
                                let un # _ = ( (applyOrErrorIO ui u vect) ) in un # lvOut

export
applyUnitaryOwnSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1_ : Unitary i) -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyUnitaryOwnSimulated lvect ui = MkUST (applyUnitaryOwn' lvect (ui))

applyInternal : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyInternal lvect ui = MkUST (applyUnitary' lvect ui)

------- below, it's the same pattern -> could be abstracted, noted for potential update --------------------

private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))->      
    (1_ : Unitary (S n)) -> LPair (Unitary (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} q ust usn = 
  let (q, k) = qubitToNatPair q in
    let vn = findInLinQ q (makeNeutralVect (S n)) in
      let un # lvOut = runUStateT (IdGate {n = n}) ust in
        let unew # _ = ( (applyOrErrorIO (controlled un) usn (k :: toVectN vn)) ) in unew # (q :: lvOut)
        

export
applyControlAbsSimulated: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))->      
    UStateT (Unitary (S n)) (Unitary (S n)) (LVect (S i) Qubit)
applyControlAbsSimulated ctrl ust = MkUST (applyControlSimulated' ctrl ust)   

public export
duplicateLinU: (1_ : Unitary n) -> Pair (Unitary n) (Unitary n)
duplicateLinU IdGate = (IdGate, IdGate)
duplicateLinU (H j g {prf} ) = let (g1,g2) = duplicateLinU g in ((H j g1 {prf = prf}), (H j g2 {prf = prf}))
duplicateLinU (P p j g {prf}) = let (g1,g2) = duplicateLinU g in ((P p j g1 {prf = prf}), (P p j g2 {prf = prf}))
duplicateLinU (CNOT c t g {prf1} {prf2} {prf3 = prf3}) = let (g1,g2) = duplicateLinU g in ((CNOT c t g1 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}), (CNOT c t g2 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}))

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect i Qubit)
applyUnitaryAbs' ust un = 
  let (un1, un2)= duplicateLinU un in 
  let (unew # lvect) = runUStateT un1 ust in
        let ufinal = compose unew un2 in
          do ufinal # (lvect)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT) 
applyUnitaryAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> UStateT (Unitary n) (Unitary n) (LVect i  Qubit)
applyUnitaryAbsSimulated ust = MkUST (applyUnitaryAbs' ust )


applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: Unitary n) -> LPair (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (un) = 
  let (un1, un2)= duplicateLinU un in -- we need this because otherwise we need a wrapper around unitary, since un is linear
  let ((unew) # lvect) = runUStateT (un1) ust in
        let unew = compose unew un2 in
          do ((unew) # (lvect))

||| Implementation of abstract split application - representationally useful
applyWithSplitLVectsSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulated ust = MkUST (applyWithSplitLVects' ust)

||| Helper for implementation of abstract controlled split application 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> (1_ : Unitary (S n)) -> LPair (Unitary (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' q ust (usn)= 
  let (un) # (lvLeft # lvRight)= runUStateT ((IdGate {n = n})) ust in
  let unew = compose (controlled un) usn in
    (unew) # ((q :: lvLeft) # lvRight)

||| Implementation of abstract controlled split application     
applyControlledSimulatedSplit: {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> UStateT (Unitary (S n)) (Unitary (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledSimulatedSplit ctrl ust = MkUST (applyControlledUSplitSim' ctrl ust)   


private
reCombineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect (i +j) Qubit))
reCombineAbs' ust (ui) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitUnitarySim ( ui) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

 
export
reCombineAbsUnitarySimulated : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (Unitary n) (Unitary n) (LVect (i+j) Qubit)
reCombineAbsUnitarySimulated q = MkUST (reCombineAbs' q)

applyParallelSimulated': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))     
                   -> (1_ : UStateT (Unitary n) (Unitary n) (LVect j Qubit))   
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect (i + j) Qubit)
applyParallelSimulated' ust1 ust2 un = 
  let (unew1# lvecti) = runUStateT IdGate ust1 in -- there are multiple choices for what order to do what in, this is one correct one
    let (unew2 # lvectj) = runUStateT IdGate ust2 in
        let unewest = compose unew1 un in
          let uOut = compose unew2 unewest in
            do (uOut # (lvecti ++ lvectj))

applyParallelSimulated: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) ((LVect i Qubit)))
                        -> (1_ : UStateT (Unitary n) (Unitary n) ((LVect j Qubit))) -> UStateT (Unitary n) (Unitary n) (LVect (i + j) Qubit)
applyParallelSimulated ust1 ust2 = MkUST (applyParallelSimulated' ust1 ust2)


export
applyHSim : {n : Nat} -> (1 _ : Qubit) -> UStateT (Unitary n) (Unitary n) (LVect 1 Qubit)
applyHSim q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryLinear.HGate)
    pure [q1]

export
applyPSim : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (Unitary n) (Unitary n) (LVect 1 Qubit)
applyPSim p q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryLinear.PGate p)
    pure [q1]

export
applyCNOTSim : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (Unitary n) (Unitary n) (LVect 2 Qubit)
applyCNOTSim q1 q2 = do
    [q1,q2] <- applyInternal {n} {i = 2} (q1::[q2]) UnitaryLinear.CNOTGate
    pure (q1::q2::[])

invert: (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit)) -> (1_ : (Unitary n)) -> LPair (Unitary n) (LVect i Qubit)
invert ust un =  
    let unOut # lvOut = runUStateT IdGate ust in
      let (invFree, invDunny) = duplicateLinU unOut in
        let invu = adjoint invFree in
          let (unFree, unDunny) = duplicateLinU un in
            let unew = compose invu unFree in
              unew # (lvOut)
 
export
adjointUST' : (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit)) -> (UStateT (Unitary n) (Unitary n) (LVect i Qubit))
adjointUST' ust = MkUST (invert ust)  
  
export
UnitaryOp Unitary where
  applyUnitary = applyUnitarySimulated
  applyUnitaryOwn = applyUnitaryOwnSimulated
  applyUnitaryAbs = applyUnitaryAbsSimulated
  applyControlledAbs = applyControlAbsSimulated
  adjointUST = adjointUST'
  applyParallel = applyParallelSimulated
  applyControlWithSplitLVects = applyControlledSimulatedSplit
  applyWithSplitLVects = applyWithSplitLVectsSimulated
  reCombineAbs = reCombineAbsUnitarySimulated
  run          = runUnitarySim 
  runSplit = runSplitUnitarySim
  applyH = applyHSim
  applyP = applyPSim
  applyCNOT = applyCNOTSim
  exportSelf = exportUnitarySelf
