module UnitarySimulated

import Data.Vect
import Data.Nat
import Data.Vect.Sort
import Decidable.Equality
import Injection
import Lemmas
import UnitaryLinear
import UStateT
import LinearTypes
import QStateT
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
||| this has to recognize and handle the case where it is applied within an abstract control
||| since this is the only was it can receive an lvect of qubits that contains an unexpected element, this is easy to handle 
||| using decidability.
private
applyUnitary' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect i Qubit))
applyUnitary' {n} {i} lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
   case decInj (n) vect of 
            Yes prfYes => let unew = (UnitaryLinear.apply ui u vect {prf = prfYes}) in unew # (lvOut)
            No prfNo => let applicable = clampUniqueWithCap n vect in -- this is only ever reached in the case of a control
                                                                          -- operation which reduced the dimension of n
                                                                          -- The operation of non-abstract-controlled operations
                                                                          -- is correct without this, feel free to edit the code and check
                        let un # _ = (applyOrErrorIO ui u (applicable)) in un # lvOut 
            --In the no case, we have a controlled applicaiton where the control qubit is small, 
            --so we index out. We can fix this by just providing the information that qubits are available
            --to the controlled operation, while keeping the LVect intact. and then allowing
            -- applyControlledAbs to use the LVect to correctly apply the controlled operation
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect (ui))


private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))->      
    (1_ : Unitary (S n)) -> LPair (Unitary (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} {i} q ust usn = 
  let (q, k) = qubitToNatPair q in
    let un # lvOut = runUStateT (IdGate {n = n}) ust in
      let lvMid # vect = distributeDupedLVectVect lvOut in
        let checkIfControl = (length (maximumControls n vect)) in
          case isGT checkIfControl 0 of 
            No prfNo => let vn = findInLin k (makeNeutralVectN (S n)) in let un # _ = (applyOrErrorIO (controlled un) usn (k::vn)) in un # (q :: lvMid)
            Yes prfYes => let v = makeNeutralVectN (S n) in let vn = findInLin k v in
              case decInj (S n) (k :: vn) of 
                Yes prfYes2 => let unew = (UnitaryLinear.apply (controlled un) usn (k :: vn ) {prf = prfYes2}) in unew # (q :: lvMid)
                No prfNo2 => let vn = findInLin k (makeNeutralVectN (S n)) in
                              let applicableSn = (k::vn) in -- this is only ever reached in the case of a multiple-control
                                                                            -- operation which reduced the dimension of n
                                                                            -- The operation of non-abstract-controlled operations
                                                                            -- is correct without this, feel free to edit the code and check
                              let un # _ = (applyOrErrorIO (controlled un) usn (applicableSn)) in un # (q :: lvMid)
            --In the no case, we have a controlled applicaiton inside a controlled application where the control qubit is small, 
            --so we index out. We can fix this by just providing the information that qubits are available
            --to the controlled operation, while keeping the LVect intact. and then allowing
            --applyControlledAbs to use the LVect to correctly apply the controlled operation -}

export
applyControlAbsSimulated: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))->      
    UStateT (Unitary (S n)) (Unitary (S n)) (LVect (S i) Qubit)
applyControlAbsSimulated ctrl ust = MkUST (applyControlSimulated' ctrl ust)   

export
duplicateLinU: (1_ : Unitary n) -> Pair (Unitary n) (Unitary n)
duplicateLinU IdGate = (IdGate, IdGate)
duplicateLinU (H j g {prf} ) = let (g1,g2) = duplicateLinU g in ((H j g1 {prf = prf}), (H j g2 {prf = prf}))
duplicateLinU (P p j g {prf}) = let (g1,g2) = duplicateLinU g in ((P p j g1 {prf = prf}), (P p j g2 {prf = prf}))
duplicateLinU (CNOT c t g {prf1} {prf2} {prf3 = prf3}) = let (g1,g2) = duplicateLinU g in ((CNOT c t g1 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}), (CNOT c t g2 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}))

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect i Qubit)
applyUnitaryAbs' ust un = 
  let (unew # lvect) = runUStateT IdGate ust in
        let ufinal = compose unew un in
          do ufinal # (lvect)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT) 
applyUnitaryAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> UStateT (Unitary n) (Unitary n) (LVect i  Qubit)
applyUnitaryAbsSimulated ust = MkUST (applyUnitaryAbs' ust )


applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: Unitary n) -> LPair (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (un) = 
    let ((unew) # lvect) = runUStateT IdGate ust in
        let unew = compose unew un in
          do ((unew) # (lvect))

||| Implementation of abstract split application - representationally useful
applyWithSplitLVectsSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulated ust = MkUST (applyWithSplitLVects' ust)

||| Helper for implementation of abstract controlled split application 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> (1_ : Unitary (S n)) -> LPair (Unitary (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' q ust (usn)= 
  let (q, k) = qubitToNatPair q in
    let un # (lvLeft # lvRight) = runUStateT (IdGate {n = n}) ust in
      let lvMid # vect = distributeDupedLVectVect (lvLeft ++ lvRight) in
        let lvOutL # lvOutR = splitLVinto i j lvMid in
        let checkIfControl = (length (maximumControls n vect)) in
          case isGT checkIfControl 0 of 
            No prfNo => let vn = findInLin k (makeNeutralVectN (S n)) in let un # _ = (applyOrErrorIO (controlled un) usn (k::vn)) in un # (q :: lvOutL # lvOutR)
            Yes prfYes => let v = makeNeutralVectN (S n) in
              let vn = findInLin k v in
                case decInj (S n) (k :: vn) of 
                  Yes prfYes => let unew = (UnitaryLinear.apply (controlled un) usn (k :: vn) {prf = prfYes}) in 
                                    unew # (q :: lvOutL # lvOutR)
                  No prfNo => let vn = findInLin k (makeNeutralVectN (S n)) in
                              let applicableSn = (k::vn) in  --same as above
                                let un # _ = (applyOrErrorIO (controlled un) usn (applicableSn)) in 
                                    un # (q :: lvOutL # lvOutR) --same as for non split control


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


private
applyUnitaryOwn' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> (1_ : Unitary i) -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect i Qubit))
applyUnitaryOwn' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
    case decInj (n) vect of 
              Yes prfYes => let unew = (UnitaryLinear.apply ui u vect {prf = prfYes}) in unew # (lvOut)
              No prfNo => let applicable = clampUniqueWithCap n vect in -- this is only ever reached in the case of a control
                                                                            -- operation which reduced the dimension of n
                                                                            -- this can be tested by using UnitaryNoPrf
                                                                            -- which works without issue
                            let un # _ = (applyOrErrorIO ui u (applicable)) in un # lvOut 

export
applyUnitaryOwnSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1_ : Unitary i) -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyUnitaryOwnSimulated lvect ui = MkUST (applyUnitaryOwn' lvect (ui))

applyInternal : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyInternal lvect ui = MkUST (applyUnitary' lvect ui)

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
  applyControlledAbs = applyControlAbsSimulated
  adjointUST = adjointUST'
  applyParallel = applyParallelSimulated
  applyControlWithSplitLVects = applyControlledSimulatedSplit
  reCombineAbs= reCombineAbsUnitarySimulated
  run          = runUnitarySim 
  applyH = applyHSim
  applyP = applyPSim
  applyCNOT = applyCNOTSim
  exportSelf = exportUnitarySelf



  {-
  ||| these cannot now be used as part of the interface, their usage is a but more roundabout:
  --runSplit = runSplitUnitarySim
  --applyWithSplitLVects = applyWithSplitLVectsSimulated
  --applyUnitaryAbs = applyUnitaryAbsSimulated

  private
makeSafeForAbstractControlVect : (1c:Nat) -> (1_ : Vect i Nat) -> (LPair (Nat) (Vect i Nat))

private
maximumControls: (n:Nat) -> (1_ : Vect i Nat) -> List Nat
maximumControls n [] = []
maximumControls n (k::ks) = case isLTE n k of
  Yes prf => k :: (maximumControls n ks)
  No prf => (maximumControls n ks)


smallestMissings : List Nat -> Vect i Nat -> List Nat
smallestMissings [] _ =  []
smallestMissings (x::xs) vect = (smallestMissing vect ) :: (smallestMissings xs vect)

makeSafe : List Nat -> Vect i Nat -> Vect i Nat
makeSafe [] vec = vec
makeSafe (c::cs) vec = let _ # vec = makeSafeForAbstractControlVect c vec in
                      makeSafe cs vec

  makeSafeForAbstractControlVect any [] = any # []
makeSafeForAbstractControlVect (Z) [Z] = (Z) # [Z] --invalid case in our context, no change
makeSafeForAbstractControlVect (Z) [(S m)] = (Z) # [m]
makeSafeForAbstractControlVect ((S m)) [Z] = ((S m)) # [Z]
makeSafeForAbstractControlVect (Z) (Z :: qs) = (Z) # (Z :: qs) --invalid case in our context, so whatever is fine
makeSafeForAbstractControlVect (Z) ((S m) :: qs) = let control # rest = makeSafeForAbstractControlVect (Z) qs in control # (m :: rest)
makeSafeForAbstractControlVect ((S k)) ((S m) :: qs) = case isLT k m of
  Yes prfYes => let control # rest = makeSafeForAbstractControlVect ((S k)) qs in control # (m :: rest)
  No prfNo => let control # rest = makeSafeForAbstractControlVect ((S k)) qs in control # ((S m):: rest)
makeSafeForAbstractControlVect ((S k)) (Z :: qs) = let control # rest = makeSafeForAbstractControlVect ((S k)) qs in control # ((Z) :: rest)

}