module SimulatedOp

import Data.Vect
import Data.Nat
import Control.Monad.State
import System.File
import Injection
import Lemmas
import UnitaryLinear
import UnitaryNoPrf
import UStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Matrix
import Data.Linear.Notation
import Data.Linear.Interface
import QuantumOp
import Complex


------ SIMULATION : AUXILIARY FUNCTIONS ------


||| we need to turn Unitary i into UnitaryNoPrf i
public export
toNoPrf : Unitary n -> UnitaryNoPrf n
toNoPrf IdGate = IdGate
toNoPrf (H j g) = (H j (toNoPrf g)) 
toNoPrf (P p j g) = (P p j (toNoPrf g))
toNoPrf (CNOT c t g) = (CNOT c t (toNoPrf g))

public export
listIndices : (1 _ : SimulatedOp n) -> (1 _ : LVect i Qubit) -> LFstPair (LPair (SimulatedOp n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y :: ys)


||| as the name suggests
lvectify : (1 _ : Vect i Qubit) -> (LVect i Qubit)
lvectify [] = []
lvectify (x :: xs) = LinearTypes.(::) x (lvectify xs)

||| merge vectors (used for deletion of duplicates)
mergeVects : (1 _ : Vect n Qubit) -> (1 _ : Vect i Qubit) -> ( LVect i Qubit)
mergeVects [] [] = []
mergeVects [] vect = lvectify vect
mergeVects (x :: xs) [] = mergeVects xs []
mergeVects (x :: xs) (y :: ys) = mergeVects xs (y::ys)

||| merge linear vectors (used for deletion of duplicates)
mergeLVects : (1 _ : LVect n Qubit) -> (1 _ : LVect i Qubit) -> (LVect i Qubit)
mergeLVects [] [] = []
mergeLVects [] lvect = lvect
mergeLVects (xs) [] = mergeVects (toVectQ xs) []
mergeLVects (xs) (ys) = mergeVects (toVectQ xs) (toVectQ ys)




||| Implementation of run for SimulatedOp
public export
run' : {i:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> LPair (SimulatedOp n) (LVect i Qubit)
run' {i = i} simop ust = runUStateT simop ust

||| Implementation of exporting self out of SimulatedOp
public export
exportSelf' : {i:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> SimulatedOp n
exportSelf' {i = i} simop ust = let op # lvect = runUStateT simop ust in
                                      let () = discardq lvect in
                                          op

||| Implementation of exporting just a unitary out of SimulatedOp
public export
exportUnitary' : {i:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> Unitary n
exportUnitary' {i = i} simop ust = let (MkSimulatedOp qn un vn counter) = exportSelf' simop ust in un

||| Implementation of runSplit SimulatedOp
public export
runSplit' : {i:Nat} -> {j:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplit' {i = i} simop ust = runUStateT simop ust

failedIoOp : {n:Nat} ->  (v: Vect i Qubit) -> (un: Unitary n) -> (ui: Unitary i) -> IO ()
failedIoOp {n} v un ui = do
        () <- putStrLn ("The vector " ++ show (toVectN v) ++ "is not Injective with respect to " ++ show n ++ ".")
        () <- putStrLn ("Therefore the application of " ++ show ui ++ " to " ++ show un ++ " could not be carried out.")
        pure () 

||| Helper for implementation of  applyUnitary
applyUnitary' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( MkUnitary (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' {n} {i} lvIn ui (MkSimulatedOp qs un v counter)= 
    let lvOut # vect = distributeDupedLVectVect lvIn in 
    case decInj (n) vect of 
              Yes prfYes => let unew = (UnitaryLinear.apply ui un vect {prf = prfYes}) in (MkSimulatedOp qs (unew) v counter) # (lvOut)
              No prfNo => let applicable = clampUniqueWithCap n vect in -- See UnitarySimulated about why and how this is needed
                                                                           -- and works; tldr is that because controlled application reduces 
                                                                           -- the dimensions, we need to do this cleverly; this point
                                                                           -- in the cf is otherwise not reached
                            let unew # _ = (applyOrErrorIO ui un (applicable)) in (MkSimulatedOp qs (unew) v counter) # lvOut 
  

||| SimulatedOp implementation of applyUnitary
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> Unitary i -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect (ui))

||| Helper for SimulatedOp implementation of applyUnitaryOwn (using self-defined datatype for unitaries)
private
applyUnitaryOwn' : {n : Nat} -> {i : Nat} -> (1 _ : SimulatedOp i) -> (1 _ : LVect i Qubit) ->
   (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitaryOwn' {n} {i} (MkSimulatedOp vacuousQS ui vacuousV vacuousC) lvIn (MkSimulatedOp qs un v counter) = 
 let lvOut # vect = distributeDupedLVectVect lvIn in 
    case decInj (n) vect of 
              Yes prfYes => let unew = (UnitaryLinear.apply ui un vect {prf = prfYes}) in (MkSimulatedOp qs (unew) v counter) # (lvOut)
              No prfNo => let applicable = clampUniqueWithCap n vect in -- See UnitarySimulated about why and how this is needed
                                                                           -- and works; tldr is that because controlled application reduces 
                                                                           -- the dimensions, we need to do this cleverly; this point
                                                                           -- in the cf is otherwise not reached
                          let unew # _ = (applyOrErrorIO ui un (applicable)) in (MkSimulatedOp qs (unew) v counter) # lvOut 
  

||| SimulatedOp implementation of applyUnitaryOwn (using self-defined datatype for unitaries)
export
applyUnitaryOwnSimulated : {n : Nat} -> {i : Nat} -> (1 _ :LVect i Qubit) -> 
  (1 _ : SimulatedOp i) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitaryOwnSimulated {n} {i} qbits simop = MkUST (applyUnitaryOwn' {n =n} {i = i} simop qbits)


||| Helper for SimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : SimulatedOp n) -> LPair (SimulatedOp n) (LVect i Qubit)
applyUnitaryAbs' ust (MkSimulatedOp qs un v counter) = 
  let ((MkSimulatedOp vacuousQS unew vnew vacuousCounter) # lvect) = runUStateT (MkSimulatedOp qs un v counter) ust in
        let unew = compose unew un in
          do ((MkSimulatedOp qs unew vnew counter) # (lvect))

||| SimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))      
                   -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i  Qubit)
applyUnitaryAbsSimulated ust = MkUST (applyUnitaryAbs' ust )


||| Auxiliary function for applying a circuit to some qubits
private
reCombineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect (i +j) Qubit))
reCombineAbs' ust (MkSimulatedOp qs us v counter) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplit' (MkSimulatedOp qs us v counter) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))
 
export
reCombineAbsSimulated : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (SimulatedOp n) (SimulatedOp n) (LVect (i+j) Qubit)
reCombineAbsSimulated q = MkUST (reCombineAbs' q)

--(1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair Qubit (LVect i Qubit))) ->

||| One must be extremelhy careful with the targets here because there are no guarantees if one wishes to do this!
private
applyControlOnly' : {n : Nat} -> {i : Nat} -> (1 _ : SimulatedOp i) -> (1 _ : Qubit) -> 
   (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect (S i) Qubit))
applyControlOnly' {n} {i} (MkSimulatedOp vacuousQS uis vi vacuousC) q (MkSimulatedOp qs un v counter) =
      let (q, k) = qubitToNatPair q in
        let unew # _ = applyOrErrorIO (controlled uis) un ((k:: (toVectN vi))) in
          do ((MkSimulatedOp qs unew v counter) # (q :: toLVectQQ vi))

--(1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair Qubit (LVect i Qubit))) ->
export
applyControlOnlySimulated : {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 _ : SimulatedOp i) ->      
    UStateT (SimulatedOp n) (SimulatedOp n) (LVect (S i) Qubit)
applyControlOnlySimulated control simop = MkUST (applyControlOnly' simop control)

||| Auxiliary function for applying a control to a UStateT
private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))->      
    (1_ : SimulatedOp (S n)) -> LPair (SimulatedOp (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} q ust (MkSimulatedOp qsn usn vsn csn)= 
  let (q, k) = qubitToNatPair q in
    let vn = findInLinQ q vsn in
      let (MkSimulatedOp dummyqs un vn dummyc) # lvOut = runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) vn n) ust in
        let lvMid # vect = distributeDupedLVectVect lvOut in
          let checkIfControl = (length (maximumControls n vect)) in
          case isGT checkIfControl 0 of 
            No prfNo => let vn = findInLin k (makeNeutralVectN (S n)) in let unew # _ = (applyOrErrorIO (controlled un) usn (k::vn)) in (MkSimulatedOp qsn unew vsn csn) # (q :: lvMid)
            Yes prfYes => let v = makeNeutralVectN (S n) in let vn = findInLin k v in
                case decInj (S n) (k :: vn) of  -- see above for reasoning
                Yes prfYes => let unew = (UnitaryLinear.apply (controlled un) usn (k :: vn ) {prf = prfYes}) in 
                                (MkSimulatedOp qsn unew vsn csn) # (q :: lvMid)
                No prfNo => let applicableSn = makeNeutralVectN (S n) in 
                                let unew # _ = (applyOrErrorIO (controlled un) usn (applicableSn)) in 
                                    (MkSimulatedOp qsn unew vsn csn) # (q :: lvMid)
  

export
applyControlAbsSimulated: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))->      
    UStateT (SimulatedOp (S n)) (SimulatedOp (S n)) (LVect (S i) Qubit)
applyControlAbsSimulated ctrl ust = MkUST (applyControlSimulated' ctrl ust)   

applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: SimulatedOp n) -> LPair (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (MkSimulatedOp qs un v counter) = 
  let ((MkSimulatedOp vacuousQS unew vnew vacuousCounter) # lvect) = runUStateT (MkSimulatedOp qs un v counter) ust in
      let unew = compose unew un in
          do ((MkSimulatedOp qs unew vnew counter) # (lvect))

||| Implementation of abstract split application - representationally useful
applyWithSplitLVectsSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulated ust = MkUST (applyWithSplitLVects' ust)

applyParallelSimulated': {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))     
                   -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect j Qubit))   
                   -> (1 _ : SimulatedOp n) -> LPair (SimulatedOp n) (LVect (i + j) Qubit)
applyParallelSimulated' ust1 ust2 (MkSimulatedOp qs un v counter) = 
  let ((MkSimulatedOp vacuousQS1 unew1 vnew1 vacuousCounter1) # lvecti) = runUStateT (MkSimulatedOp qs IdGate v counter) ust1 in -- there are multiple choices for what order to do what in, this is one correct one
    let ((MkSimulatedOp vacuousQS2 unew2 vnew2 vacuousCounter2) # lvectj) = runUStateT (MkSimulatedOp qs IdGate v counter) ust2 in
        let unewest = compose unew1 un in
          let uOut = compose unew2 unewest in
            do ((MkSimulatedOp qs uOut vnew2 counter) # (lvecti ++ lvectj))

applyParallelSimulated: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) ((LVect i Qubit)))
                        -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) ((LVect j Qubit))) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect (i + j) Qubit)
applyParallelSimulated ust1 ust2 = MkUST (applyParallelSimulated' ust1 ust2)

||| Helper for implementation of abstract controlled split application 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> (1_ : SimulatedOp (S n)) -> LPair (SimulatedOp (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' q ust (MkSimulatedOp qsn usn vsn csn)= 
  let (q, k) = qubitToNatPair q in
    let vn = findInLinQ q vsn in
      let (MkSimulatedOp dummyqs un vn dummyc) # (lvLeft # lvRight) = runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) vn n) ust in
        let lvMid # vect = distributeDupedLVectVect (lvLeft ++ lvRight) in
          let lvOutL # lvOutR = splitLVinto i j lvMid in
            let checkIfControl = (length (maximumControls n vect)) in
          case isGT checkIfControl 0 of 
            No prfNo => let vn = findInLin k (makeNeutralVectN (S n)) in let unew # _ = (applyOrErrorIO (controlled un) usn (k::vn)) in (MkSimulatedOp qsn unew vsn csn)  # (q :: lvOutL # lvOutR)
            Yes prfYes => let v = makeNeutralVectN (S n) in
              let vn = findInLin k v in
                case decInj (S n) (k :: vn) of 
                Yes prfYes => let unew = (UnitaryLinear.apply (controlled un) usn (k :: vn) {prf = prfYes}) in 
                                    (MkSimulatedOp qsn unew vsn csn) # (q :: lvOutL # lvOutR)
                No prfNo => let applicableSn = makeNeutralVectN (S n) in --same as above
                                let unew # _ = (applyOrErrorIO (controlled un) usn (applicableSn)) in 
                                    (MkSimulatedOp qsn unew vsn csn) # (q :: lvOutL # lvOutR) --same as for non split control


||| Implementation of abstract controlled split application     
applyControlledSimulatedSplit: {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> UStateT (SimulatedOp (S n)) (SimulatedOp (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledSimulatedSplit ctrl ust = MkUST (applyControlledUSplitSim' ctrl ust)   


invert: (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1_ : (SimulatedOp n)) -> LPair (SimulatedOp n) (LVect i Qubit)
invert ust (MkSimulatedOp qn u v counter)=  
    let (MkSimulatedOp dummyqs un vn dummyc) # lvOut = runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) v counter) ust in
        let invu = adjoint un in
            let unew = compose invu u in
                (MkSimulatedOp qn unew v counter) # (lvOut)
export
adjointUST' : (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))
adjointUST' ust = MkUST (invert ust)

-------------------------------------------------------------------------
||| Other situationally useful, but not necessary interface functions

neutralOp : UnitaryOp t => {n : Nat} -> ((t n)) 

neutralWithQubits : UnitaryOp t => {n : Nat} -> (1 _ : LVect n Qubit) -> (LPair (t n) (LVect n Qubit))

||| sequence with dummy (t n) used for only constructing unitaries
runNeutral : UnitaryOp t =>  {n : Nat} -> (1_ : UStateT (t n) (t n) (LVect n Qubit) ) -> (LPair (t n) (LVect n Qubit))

||| sequence over a given vector of qubits in (t n) used for only constructing unitaries
runNeutralAt : UnitaryOp t =>  {n : Nat} -> (1 _ : LVect n Qubit) -> (1_ : UStateT (t n) (t n) (LVect n Qubit) ) -> (LPair (t n) (LVect n Qubit))

neutralWithQubits' : UnitaryOp t => {n : Nat} -> (1 _ : LVect n Qubit) -> LPair (SimulatedOp n) (LVect n Qubit) 
neutralWithQubits' {n} lvect = let lvOut # v = distributeDupedLVectVect lvect in 
  (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (fromVectN v) n) # lvOut

public export
runNeutralAt' :  UnitaryOp t => {n : Nat} -> (1 _ : LVect n Qubit) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect n Qubit) ) -> LPair (SimulatedOp n) (LVect n Qubit)
runNeutralAt' {n} lvIn ust = 
    let lvInt # vect = distributeDupedLVectVect lvIn in
      let simOut # lv = runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (fromVectN vect) n) ust 
          lvOut = mergeLVects lvInt lv in
          simOut # lvOut

||| Apply the controlled version of a unitary in t n without explicit list (taking it from t n). Implementations assume control goes at head of qubit list
||| This requires that the ownUnitary be built so that it is applicable to the i qubits within n it is specified for
||| This isn;t necessarily possible to do, so it does not form a part of the interface, but it is useful.
applyControlledOwn :UnitaryOp t =>  {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 ownUnitary : t i) -> UStateT (t n) (t n) (LVect (S i) Qubit) --> (1 _ :LVect i Qubit) 

|||Helper 
private
applyControlledUnitaryOwn' : {n : Nat} -> {i : Nat} -> (1 _ : SimulatedOp i) -> (1 _ : Qubit) -> 
   (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect (S i) Qubit))
applyControlledUnitaryOwn' {n} {i} (MkSimulatedOp vacuousQS ui vi vacuousC) q (MkSimulatedOp qs un vn counter) =
  let (q, k) = qubitToNatPair q in
    let vin = toVectN vi in
      let unew # _ = UnitaryLinear.applyOrErrorIO (controlled ui) un (k :: (vin)) in
        do ((MkSimulatedOp qs unew vn counter) # (q :: (toLVectQ vin)))
           

||| Implementation of 
export
applyControlledOwnSimulated : {n : Nat} -> {i : Nat} -> (1 _ : Qubit) ->
                   (1_ : SimulatedOp i) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect (S i) Qubit) 
applyControlledOwnSimulated control simop= MkUST (applyControlledUnitaryOwn' simop control )
--------------------------------------------------------------------------


export
UnitaryOp SimulatedOp where
  applyUnitary = applyUnitarySimulated
  applyUnitaryOwn = applyUnitaryOwnSimulated
  applyControlledAbs = applyControlAbsSimulated
  applyParallel = applyParallelSimulated 
  adjointUST = adjointUST'
  applyControlWithSplitLVects = applyControlledSimulatedSplit
  reCombineAbs= reCombineAbsSimulated
  run          = run' 
  exportSelf = exportSelf'

-------------------------------------------------------------------------

{-
  ||| these cannot now be used as part of the interface, their usage is a but more roundabout:
    --runSplit = runSplit'
    --applyWithSplitLVects = applyWithSplitLVectsSimulated
    --applyUnitaryAbs = applyUnitaryAbsSimulated
-}