module UnitaryNoPrfSim

import Data.Vect
import Data.Nat
import Control.Monad.State
import Decidable.Equality
import System.File
import Injection
import Matrix
import UnitaryOp
import Complex
import Lemmas
import UnitaryNoPrf
import UnitaryLinear
import UStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Data.Maybe
import QStateT
import Data.Linear.Notation
import Data.Linear.Interface
import Qubit


public export
runUnitaryNoPrfSim : {i:Nat} -> (1_: UnitaryNoPrf n) -> (1 _ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit) ) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
runUnitaryNoPrfSim {i = i} simop ust = runUStateT simop ust


public export
exportSelf' : {i:Nat} -> (1_: UnitaryNoPrf n) -> (1 _ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit) ) -> UnitaryNoPrf n
exportSelf' {i = i} simop ust = let unprf # lvect = runUStateT simop ust in
                                      let () = discardq lvect in
                                          unprf

public export
runSplitUnitaryNoPrfSim : {i:Nat} -> {j:Nat} -> (1_: UnitaryNoPrf n) -> (1 _ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitUnitaryNoPrfSim {i = i} simop ust = runUStateT simop ust

||| Auxiliary function for applying a circuit to some qubits
private
applyUnitaryNoPrf' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> UnitaryNoPrf i -> (1 _ : UnitaryNoPrf n) -> (LPair (UnitaryNoPrf n) (LVect i Qubit))
applyUnitaryNoPrf' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut

export
applyUnitaryNoPrfSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)
applyUnitaryNoPrfSimulated lvect ui = MkUST (applyUnitaryNoPrf' lvect (toNoPrf ui))

private
applyUnitaryNoPrfOwn' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) -> (1 _ : UnitaryNoPrf n) -> (LPair (UnitaryNoPrf n) (LVect i Qubit))
applyUnitaryNoPrfOwn' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut

export
applyUnitaryNoPrfOwnSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)
applyUnitaryNoPrfOwnSimulated lvect ui = MkUST (applyUnitaryNoPrfOwn' lvect (ui))

applyInternal : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> UnitaryNoPrf i -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)
applyInternal lvect ui = MkUST (applyUnitaryNoPrf' lvect ui)

------- below, it's the same pattern -> could be abstracted, noted for potential update --------------------

private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))->      
    (1_ : UnitaryNoPrf (S n)) -> LPair (UnitaryNoPrf (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} q ust usn = 
  let (q, k) = qubitToNatPair q in
    let vn = findInLinQ q (makeNeutralVect (S n)) in
        let un # lvOut = runUStateT (IdGate {n = n}) ust in
            let unew = UnitaryNoPrf.apply (controlled un) usn (k :: toVectN vn) in
                unew # (q :: lvOut)

export
applyControlAbsSimulated: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))->      
    UStateT (UnitaryNoPrf (S n)) (UnitaryNoPrf (S n)) (LVect (S i) Qubit)
applyControlAbsSimulated ctrl ust = MkUST (applyControlSimulated' ctrl ust)   

public export
duplicateLinU: (1_ : UnitaryNoPrf n) -> Pair (UnitaryNoPrf n) (UnitaryNoPrf n)
duplicateLinU IdGate = (IdGate, IdGate)
duplicateLinU (H j g  ) = let (g1,g2) = duplicateLinU g in ((H j g1), (H j g2 ))
duplicateLinU (P p j g ) = let (g1,g2) = duplicateLinU g in ((P p j g1), (P p j g2 ))
duplicateLinU (CNOT c t g) = let (g1,g2) = duplicateLinU g in ((CNOT c t g1), (CNOT c t g2))

||| Helper for UnitaryNoPrf implementation of abstract UnitaryNoPrf application (that is, whatever one built using UStateT)
applyUnitaryNoPrfAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
applyUnitaryNoPrfAbs' ust un = 
  let (un1, un2)= duplicateLinU un in 
  let (unew # lvect) = runUStateT un1 ust in
        let ufinal = UnitaryNoPrf.compose unew un2 in
          do ufinal # (lvect)

||| UnitaryNoPrf implementation of abstract UnitaryNoPrf application (that is, whatever one built using UStateT) 
applyUnitaryNoPrfAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i  Qubit)
applyUnitaryNoPrfAbsSimulated ust = MkUST (applyUnitaryNoPrfAbs' ust )


applyUnitaryNoPrfAbsSplit' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))
applyUnitaryNoPrfAbsSplit' ust (un) = 
  let (un1, un2)= duplicateLinU un in -- we need this because otherwise we need a wrapper around UnitaryNoPrf, since un is linear
  let ((unew) # lvect) = runUStateT (un1) ust in
        let unew = UnitaryNoPrf.compose unew un2 in
          do ((unew) # (lvect))

||| Implementation of abstract split application - representationally useful
applyUnitaryNoPrfAbsSplitSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))
applyUnitaryNoPrfAbsSplitSimulated ust = MkUST (applyUnitaryNoPrfAbsSplit' ust)

||| Helper for implementation of abstract controlled split application 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> (1_ : UnitaryNoPrf (S n)) -> LPair (UnitaryNoPrf (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' q ust (usn)= 
  let (un) # (lvLeft # lvRight)= runUStateT ((IdGate {n = n})) ust in
  let unew = UnitaryNoPrf.compose (controlled un) usn in
    (unew) # ((q :: lvLeft) # lvRight)

||| Implementation of abstract controlled split application     
applyControlledSimulatedSplit: {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> UStateT (UnitaryNoPrf (S n)) (UnitaryNoPrf (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledSimulatedSplit ctrl ust = MkUST (applyControlledUSplitSim' ctrl ust)   


private
reCombineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : UnitaryNoPrf n) -> (LPair (UnitaryNoPrf n) (LVect (i +j) Qubit))
reCombineAbs' ust (ui) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitUnitaryNoPrfSim ( ui) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

 
export
reCombineAbsUnitaryNoPrfSimulated : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i+j) Qubit)
reCombineAbsUnitaryNoPrfSimulated q = MkUST (reCombineAbs' q)

export
applyHSim : {n : Nat} -> (1 _ : Qubit) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect 1 Qubit)
applyHSim q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryNoPrf.HGate)
    pure [q1]

export
applyPSim : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect 1 Qubit)
applyPSim p q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryNoPrf.PGate p)
    pure [q1]

export
applyCNOTSim : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect 2 Qubit)
applyCNOTSim q1 q2 = do
    [q1,q2] <- applyInternal {n} {i = 2} (q1::[q2]) UnitaryNoPrf.CNOTGate
    pure (q1::q2::[])

private
invertNoPrf: (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)) -> (1_ : (UnitaryNoPrf n)) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
invertNoPrf ust un =  
    let unOut # lvOut = runUStateT IdGate ust in
      let (invFree, invDunny) = duplicateLinU unOut in
        let invu = adjoint invFree in
          let (unFree, unDunny) = duplicateLinU un in
            let unew = compose invu unFree in
              unew # (lvOut)
 
export
adjointUSTNoPrf' : (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)) -> (UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))
adjointUSTNoPrf' ust = MkUST (invertNoPrf ust)

applyParallelSimulatedNoPrf': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))     
                   -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect j Qubit))   
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyParallelSimulatedNoPrf' ust1 ust2 un = 
    let (unew1 # lvecti) = runUStateT IdGate ust1 in
      let (unew2 # lvectj) = runUStateT IdGate ust2 in
        let umed = UnitaryNoPrf.compose unew1 un in
          let ufinal = UnitaryNoPrf.compose unew2 umed in
            do ufinal # (lvecti ++ lvectj)

export 
applyParallelSimulatedNoPrf: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) ((LVect i Qubit)))
                        -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) ((LVect j Qubit))) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyParallelSimulatedNoPrf ust1 ust2 = MkUST (applyParallelSimulatedNoPrf' ust1 ust2)
  
export
UnitaryOp UnitaryNoPrf where
  applyUnitary = applyUnitaryNoPrfSimulated
  applyUnitaryOwn = applyUnitaryNoPrfOwnSimulated
  applyUnitaryAbs = applyUnitaryNoPrfAbsSimulated
  applyControlledAbs = applyControlAbsSimulated
  adjointUST = adjointUSTNoPrf'
  applyPrallel= applyParallelSimulatedNoPrf
  --applyControlWithSplitLVects = applyControlledSimulatedSplit
  --applyWithSplitLVects = applyUnitaryNoPrfAbsSplitSimulated
  --reCombineAbs = reCombineAbsUnitaryNoPrfSimulated
  run          = runUnitaryNoPrfSim 
  --runSplit = runSplitUnitaryNoPrfSim
  applyH = applyHSim
  applyP = applyPSim
  applyCNOT = applyCNOTSim