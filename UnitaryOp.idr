module UnitaryOp

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
import Qubit
import Complex


||| The UnitaryOpBad interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Qubits it contains.
public export
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} -> 
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a user-implemented unitary circuit to the Qubits specified by the Vect argument
  ||| since t n must implement unitaries, it works perfectly here.
  ||| liner in ownUnitary because this way results of "run" can be used
  applyUnitaryOwn : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) -> (1 ownUnitary : t i) -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a user-implemented unitary circuit to the Qubits specified by the Vect argument  
  ||| This is essentially the same as just sequencing normally, and is mostly only representationally helpful           
  applyUnitaryAbs: {n : Nat} -> {i : Nat} -> (1_ : UStateT (t n) (t n) (LVect i Qubit))      
                   -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single Qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure [q1]

  ||| Apply a P gate to a single Qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure [q1]

  ||| Apply the CNOT gate to a pair of Qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1::q2::[])
  
  ||| apply a controlled version of a UStateT built using the interface
  ||| since there is a control we have to take from n, the UStateT used at most has n (if i = n) qubits 
  ||| i.e. it is one qubit smaller than the controlled version, which is therefore a larger UStateT
  ||| This will usually be fulfulled automatically by construction
  applyControlledAbs: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (t n) (t n) (LVect i Qubit))      
                   -> UStateT (t (S n)) (t (S n)) (LVect (S i) Qubit)

  ||| Abstract split application: helps with constructing circuits with parallel applications recursively (i.e. tensoring)
  applyParallel: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (t n) (t n) ((LVect i Qubit)))
                        -> (1_ : UStateT (t n) (t n) ((LVect j Qubit))) -> UStateT (t n) (t n) (LVect (i + j) Qubit)
  
  adjointUST: (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (UStateT (t n) (t n) (LVect i Qubit))

  ||| sequence to the end
  run :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit) ) -> (LPair (t n) (LVect i Qubit))

  exportSelf :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (t n)
  exportSelf {i = i} tn ust = let tnout # lvect = runUStateT tn ust in
                                      let () = discardq lvect in
                                          tnout



------------- OTHER UTILITIES ------------
||| WHILE NOT STRICTLY A PART OF THE INTERFACE
||| IT IS HIGHLY RECOMMENDED THAT THESE 
||| UTILIZED, AS THEY MAKE LIFE A LOT EASIER
------------------------------------------

||| for exporting an instance opf the Unitary algebraic datatype based on the unitary build inside UStateT
||| this is not in general doable, as it depends on the structure of the specific t n and whether it can be translated into 
||| a value of Unitary n, because the proofs are necessary to build an instance of the type
export
exportUnitary : UnitaryOp t => {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (Unitary n)

  --------------------- Split Computation and Accompanying Utilities -------------------------

||| sequence to the end with split computation
public export
runSplit :  UnitaryOp t => {i : Nat} -> {j:Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)) ) 
            -> (LPair (t n) (LPair (LVect i Qubit) (LVect j Qubit)))

public export            
||| Abstract split application: Convenience function for avoiding proofs when dealing with multiple qubit list inputs/ancillae
applyWithSplitLVects : UnitaryOp t => {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
                        -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))
public export
||| Apply the controlled version of a unitary. Implementations assume control goes at head of lvect list
applyControlWithSplitLVects : UnitaryOp t => {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
                            -> UStateT (t (S n)) (t (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))

public export
|||recombine split computation
reCombine : UnitaryOp t => {i:Nat} -> {j:Nat} ->  {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect j Qubit) -> UStateT (t n) (t n) (LVect (i+j) Qubit)
reCombine {i=i} is js =  pure $ LinearTypes.(++) is js  
public export
||| Abstract recombination
reCombineAbs : UnitaryOp t => {i:Nat} -> {j:Nat} -> {n : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))) 
              -> UStateT (t n) (t n) (LVect (i + j) Qubit)
  --------------------------------------------------------------------------------

||| SWAP registers in parsing; an exchange of "wires", easy to make conditional 
export                           
swapRegistersSplit : UnitaryOp t => {i:Nat} -> {j:Nat}  -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect j Qubit) -> UStateT (t n) (t n) (LPair (LVect j Qubit) (LVect i Qubit))
swapRegistersSplit qs rs = pure $ rs # qs

||| SWAP registers in parsing; an exchange of "wires", easy to make conditional 
export                           
swapRegistersSplitEq : UnitaryOp t =>  {i:Nat}  -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect i Qubit))
swapRegistersSplitEq qs rs = pure $ rs # qs

|||recombine split computation, adding one qubit to the end
export
reCombineSingleR :UnitaryOp t =>  {i:Nat} -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
reCombineSingleR {i=Z} [] q =  pure $ [q]
reCombineSingleR {i=i} is q =  pure $ (rewrite sym $ lemmaplusOneRightHC {n = i} in (LinearTypes.(++) is [q]))

||| recombine split computation, adding one qubit to the beginning
export
reCombineSingleL : UnitaryOp t => {i:Nat}  -> {n : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
reCombineSingleL {i=Z} q [] =  pure $ [q]
reCombineSingleL {i=i} q is = pure $ (q :: is)

%hint
export
singleQubit : (1 _ : LVect 1 Qubit)-> Qubit
singleQubit [q] = q

public export total
splitFirstUtil : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect 1 Qubit) (LVect i Qubit))
splitFirstUtil {i = Z} [] impossible
splitFirstUtil {i = Z} [as] = pure $ [as] # []
splitFirstUtil {i = (S Z)} [a,b] = pure $ [a] # [b]
splitFirstUtil {i = (S (S k))} (a::as) = do
    pure $ [a] # (as)

|||get the First qubit from a list of qubits
public export total
splitLastUtil : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect 1 Qubit))
splitLastUtil {i = Z} {n = n} [] impossible
splitLastUtil {i = Z} {n = n} [as] = pure $ [] # [as]
splitLastUtil {i = (S Z)} {n = n} [a,b] = pure $ [a] # [b]
splitLastUtil {i = (S (S k))} {n = n} (a::as) = do
    as # last <- splitLastUtil (as)
    pure $ (a :: as) # last
    
||| split qubits at index. careful with proofs 
public export
splitQubitsAt : UnitaryOp t => {i: Nat} -> {n : Nat} -> (k: Nat) -> {auto prf: LT k i} -> (1_ : LVect i Qubit) 
                            -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect (minus i k) Qubit))
splitQubitsAt k [] = absurd prf
splitQubitsAt 0 any  = pure $ [] # (rewrite minusZeroRight i in any)
splitQubitsAt (S k) (a::as) = do
    as # ass <- splitQubitsAt k (as)
    pure $ ((a :: as)) # ass

||| split qubits at index
public export
splitQubitsInto : UnitaryOp t => {i: Nat} -> {n : Nat} -> (k: Nat) -> (r:Nat) -> {auto prf: k + r = i} -> (1_ : LVect i Qubit) 
                            -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect r Qubit))
splitQubitsInto 0 0 [] = pure $ [] # []
splitQubitsInto 0 0 (a::as) impossible
splitQubitsInto {prf} 0 r any = (pure $ [] # (rewrite prf in any))
splitQubitsInto k 0 any = pure $ (rewrite sym $ plusZeroRightNeutral k in (rewrite prf in any)) # []
splitQubitsInto {prf = prf} {i = S h} (S k) (S r) (a::as) = do
    as # ass <- splitQubitsInto {prf = succInjective (rewrite plusSuccLeftSucc (k) (S r) in prf)}k (S r) (as)
    pure $ ((a :: as)) # ass

public export    
splitLVinto : (n : Nat) -> (k: Nat) -> (1_ : LVect (n + k) Qubit) 
                            -> (LPair (LVect n Qubit) (LVect k Qubit))
splitLVinto  0 0 [] = [] # []
splitLVinto 0 0 (a::as) impossible
splitLVinto  0 k any = [] # any
splitLVinto  n 0 any = (rewrite sym $ plusZeroRightNeutral n in any) # []
splitLVinto (S m) (S r) (a::as) = let as # ass = splitLVinto m (S r) (as) in (a::as) # ass


public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> Unitary n -> Vect n Qubit -> Nat -> SimulatedOp n


------ SIMULATION : AUXILIARY FUNCTIONS ------


||| we need to turn Unitary i into UnitaryNoPrf i
public export
toNoPrf : Unitary n -> UnitaryNoPrf n
toNoPrf IdGate = IdGate
toNoPrf (H j g) = (H j (toNoPrf g)) 
toNoPrf (P p j g) = (P p j (toNoPrf g))
toNoPrf (CNOT c t g) = (CNOT c t (toNoPrf g))

public export
listIndex : (1 _ : SimulatedOp n) -> (1 _ : Qubit) -> LFstPair (LPair (SimulatedOp n) Qubit) Nat
listIndex (MkSimulatedOp qs us v counter) q = let (q, k) = qubitToNatPair q in
        (MkSimulatedOp qs us v counter # q) # (listIndex' v q)

public export
listIndices : (1 _ : SimulatedOp n) -> (1 _ : LVect i Qubit) -> LFstPair (LPair (SimulatedOp n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y :: ys)

||| Remove an element at a given index in the vector
public export
removeElem : {n : Nat} -> Vect (S n) Qubit -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k

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

||| Implementation of exporting just a unitary out of SimulatedOp
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
    case decInj n vect of
      Yes prfInj => (MkSimulatedOp qs ((apply (ui) un vect)) v counter) # lvOut
      No prfNotInj => (MkSimulatedOp qs (un) v counter) # lvOut
  

||| SimulatedOp implementation of applyUnitary
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> Unitary i -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect (ui))

||| Helper for SimulatedOp implementation of applyUnitaryOwn (using self-defined datatype for unitaries)
private
applyUnitaryOwn' : {n : Nat} -> {i : Nat} -> (1 _ : SimulatedOp i) -> (1 _ : LVect i Qubit) ->
   (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitaryOwn' {n} {i} (MkSimulatedOp vacuousQS uis vacuousV vacuousC) lvIn (MkSimulatedOp qs un v counter) = 
    let lvOut # vect = distributeDupedLVectVect lvIn in 
      let unew = apply uis un (vect) in
        do ((MkSimulatedOp qs unew v counter) # (lvOut))

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
reCombineAbs' ust (MkSimulatedOp qs us v counter) = let (Builtin.(#) opOut (lvect #rvect)) = (UnitaryOp.runSplit' (MkSimulatedOp qs us v counter) ust) in do
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
        let unew = apply (controlled uis) un ((k:: (toVectN vi))) in
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
        let unew = apply (controlled un) usn (k :: (toVectN vn)) in
            (MkSimulatedOp qsn unew vsn csn) # (q :: lvOut)

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
      let (MkSimulatedOp dummyqs un vn dummyc) # (lvLeft # lvRight)= runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) vn n) ust in
        let unew = apply (controlled un) usn (k :: (toVectN vn)) in
          (MkSimulatedOp qsn unew vsn csn) # ((q :: lvLeft) # lvRight)

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

neutralOp' : UnitaryOp t => {n:Nat} -> SimulatedOp n
neutralOp' {n} = (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (makeNeutralVect n) n)

neutralWithQubits' : UnitaryOp t => {n : Nat} -> (1 _ : LVect n Qubit) -> LPair (SimulatedOp n) (LVect n Qubit) 
neutralWithQubits' {n} lvect = let lvOut # v = distributeDupedLVectVect lvect in 
  (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (fromVectN v) n) # lvOut

runNeutral' :  UnitaryOp t => {n : Nat} -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect n Qubit) ) -> LPair (SimulatedOp n) (LVect n Qubit)
runNeutral' {n} ust = runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (makeNeutralVect n) n) ust

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
      let unew = apply (controlled ui) un (k :: (vin)) in
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
  applyUnitaryAbs = applyUnitaryAbsSimulated
  applyControlledAbs = applyControlAbsSimulated
  applyParallel = applyParallelSimulated 
  adjointUST = adjointUST'
  
  run          = run' 
  exportSelf = exportSelf'

-------------------------------------------------------------------------



{-}applyControlWithSplitLVects = applyControlledSimulatedSplit
applyWithSplitLVects = applyWithSplitLVectsSimulated
reCombineAbs = reCombineAbsSimulated
runSplit = runSplit'
    let ((MkSimulatedOp vacuousQS ui vi vacuousCounter) # lvect) = (UnitaryOp.run' (MkSimulatedOp (neutralIdPow i) (IdGate {n = i}) (fromVectN vect) i) ust) in
    let lvOut = (mergeLVects lvect lvInt) 
        lvFin # vect = distributeDupedLVectVect lvOut
        cvect = k :: vect 
       in MkUST (applyUnitaryOwn' {n =n} {i = S i} (MkSimulatedOp (neutralIdPow (S i)) (controlled (ui)) (fromVectN cvect) vacuousCounter) ((MkQubit k) ::lvFin))
    
    -}
    
  {-}
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' v u (MkSimulatedOp {n = n} qs us vs counter) = 
  let (qs # v') # ind = listIndices (MkSimulatedOp {n = n} qs us vs counter) v 
      qs2 = applyCirc ind u qs
  in (qs2 # v') where
    applyCirc : {n : Nat} -> Vect i Nat -> Unitary i -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v IdGate qst = qst
    applyCirc {n = n} v (H j g) st = 
      let k = indexLT j v 
          h = simpleTensor matrixH n k
          MkSimulatedOp qst ust q counter = applyCirc v g st
      in MkSimulatedOp {n = n} qst (h `matrixMult` ust) q counter
    applyCirc {n = n} v (P p j g) st = 
      let k = indexLT j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedOp qst ust q counter = applyCirc v g st
      in MkSimulatedOp {n = n} qst (ph `matrixMult` ust) q counter
    applyCirc {n = n} v (CNOT c t g) st = 
      let kc = indexLT c v
          kt = indexLT t v
          cn =  tensorCNOT n kc kt
          MkSimulatedOp qst ust q counter = applyCirc v g st
      in MkSimulatedOp qst (cn `matrixMult` ust) q counter  

||| Auxiliary function for applying a circuit to some qubits

private
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' v u q = 
  let (qs # v') # ind = listIndices q v 
      qs2 = applyCirc ind u qs
  in (qs2 # v') where
    applyCirc : Vect i Nat -> Unitary i -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v IdGate qst = qst
    applyCirc v (H j g) st = 
      let k = indexLT j v 
          h = simpleTensor matrixH n k
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let k = indexLT j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let kc = indexLT c v
          kt = indexLT t v
          cn =  tensorCNOT n kc kt
          MkSimulatedOp qst q counter = applyCirc v g st
      in MkSimulatedOp (cn `matrixMult` qst) q counter
    -}


{-}
applytU' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Qubit) -> (SimulatedOp i) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applytU' v u q = 
  let (qs # v') # ind = listIndices q v 
      qs2 = applyCirc ind u qs
  in (qs2 # v') where
    applyCirc : Vect i Nat -> (SimulatedOp i) -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v (MkSimulatedOp ui qi ci) (MkSimulatedOp qst qn cn) = 
          MkSimulatedOp ((tensorUp ui n qi)`matrixMult` qst) qn cn

applyUnitaryTSim : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (SimulatedOp i) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitaryTSim lvect simi = MkUST (applytU' lvect simi)

applyHAbs' : {n : Nat} -> (1 _ : Qubit) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect 1 Qubit))
applyHAbs' v q = 
  let 
    (qs # v') # ind = listIndices q [v] 
    qs2 = applyHAux ind qs
    in 
      (qs2 # v') where
        applyHAux : Vect 1 Nat -> (1 _ : SimulatedOp n) -> SimulatedOp n
        applyHAux [v] (MkSimulatedOp qst q counter) = 
          let 
          h = simpleTensor matrixH n v
          in 
            MkSimulatedOp (h `matrixMult` qst) q counter

applyHSim : {n : Nat} -> 
(1 _ : Qubit) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect 1 Qubit)
applyHSim q = MkUST (applyHAbs' q)


applyPAbs' : {n : Nat} -> Double -> (1 _ : Qubit) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect 1 Qubit))
applyPAbs' d v q = 
  let 
    (qs # v') # ind = listIndices q [v] 
    qs2 = applyPAux ind d qs
    in 
      (qs2 # v') where
        applyPAux : Vect 1 Nat -> Double -> (1 _ : SimulatedOp n) -> SimulatedOp n
        applyPAux [v] d (MkSimulatedOp qst q counter) = 
          let 
          h = simpleTensor (matrixP d) n v
          in 
            MkSimulatedOp (h `matrixMult` qst) q counter

applyPSim : {n : Nat} -> Double ->
(1 _ : Qubit) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect 1 Qubit)
applyPSim d q = MkUST (applyPAbs' d q)

applyCNOTAbs' : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect 2 Qubit))
applyCNOTAbs' q1 q2 q = 
  let 
    (qs # v') # ind = listIndices q [q1, q2] 
    qs2 = applyCNOTAux ind qs
    in 
      (qs2 # v') where
        applyCNOTAux : Vect 2 Nat -> (1 _ : SimulatedOp n) -> SimulatedOp n
        applyCNOTAux [v1, v2] (MkSimulatedOp qst q counter) = 
          let 
          h = tensorCNOT n v1 v2
          in 
            MkSimulatedOp (h `matrixMult` qst) q counter

applyCNOTSim : {n : Nat} -> (1 _ : Qubit) ->
(1 _ : Qubit) -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect 2 Qubit)
applyCNOTSim q1 q2 = MkUST (applyCNOTAbs' q1 q2)
-}

{-}
newControl : {n : Nat} -> {i : Nat} -> -> (1 _ : Qubit) -> (1_ :LVect i Qubit) -> 
          (1_ : UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect (S i) Qubit))
newControl c (MkUst f) (MkSimulatedOp qs un v counter) =
  let lvOut # vect = distributeDupedLVectVect qbits in
    let ((MkSimulatedOp vacuousQS ui vi vacuousCounter) # lvect) = (run (MkSimulatedOp (neutralIdPow i) (IdGate {n = i}) (fromVectN vect) i) ust) in
    -}

{-}
private
applyControl' : {n : Nat} -> {i : Nat} -> (1 _ : Qubit) ->
  (1_ : UStateT (SimulatedOp (S n)) (SimulatedOp (S n)) (LVect i Qubit)) -> (1 _ : SimulatedOp (n)) -> (LPair (SimulatedOp (S n)) (LVect (S i) Qubit))
applyControl' (MkQubit k) ust (MkSimulatedOp qs ui v counter) = 
  let ((MkSimulatedOp dunnyqs unew vnew counter) # lvOut) = run' (MkSimulatedOp (neutralIdPow (S n)) (controlled ui) ((MkQubit k)::v) counter) ust in
    do ((MkSimulatedOp qs unew vnew counter) # ((MkQubit k) :: lvOut ))
    --let (Builtin.(#) opOut lvect) = (runUnitarySim ((controlled ui) ust)) in do (Builtin.(#) opOut (q ::lvect ))

 
export
applyControlSimulated : {n : Nat} -> {i : Nat} -> (1_ : Qubit) ->
  (1_ : (UStateT (SimulatedOp (S n)) (SimulatedOp (S n)) (LVect i Qubit) )) -> UStateT (SimulatedOp n) (SimulatedOp (S n)) (LVect (S i) Qubit)
applyControlSimulated control q = MkUST (applyControl' control q)


private
applyControlledSplit' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1 _ : Qubit) ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))) 
  -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LPair (LVect (S (i)) Qubit) (LVect j Qubit)))
applyControlledSplit' q ust (MkSimulatedOp qs us v counter) = let (Builtin.(#) opOut (lvect # rvect)) = (UnitaryOp.runSplit' (MkSimulatedOp qs us v counter) ust) in do
 (Builtin.(#) opOut ((q ::lvect) # rvect))
  
export
applyControlledSimulatedSplit : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : Qubit) ->
  (1_ : (UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))) 
  -> UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect (S i) Qubit) (LVect j Qubit))
applyControlledSimulatedSplit control q = MkUST (applyControlledSplit' control q)


applyUnitary' : {n : Nat} -> {i : Nat} -> {k : Nat} -> {r : Nat} -> (1 _ : LVect k Qubit) -> (1 _ : LVect r Qubit) 
                -> (1 _ : SimulatedOp n) -> (1 _ : SimulatedOp p) -> (LPair (SimulatedOp (n+p)) (LVect (k+r) Qubit))

applyTensorSim : {n : Nat} -> {p : Nat} -> {k : Nat} -> {r : Nat} 
              -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect k Qubit))-> (1_ : UStateT (SimulatedOp p) (SimulatedOp p) (LVect rQubit)) 
              -> (1_ : UStateT (SimulatedOp (n+p)) (SimulatedOp (n+p)) (LVect (k+r) Qubit))
applyTensorSim (MkUST f) (MkUst g)
              
public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> (1_: Vect n Qubit) -> Nat -> SimulatedOp n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------

||| Find an element in a list : used to find the wire of a qubit
export
listIndex' : {n : Nat} -> (1_: Vect n Qubit) -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

export
listIndex : (1 _ : SimulatedOp n) -> (1 _ : Qubit) -> LPair (LPair (SimulatedOp n) Qubit) Nat
listIndex (MkSimulatedOp qs us v counter) (MkQubit k) = let MkPair v' v'' = toVectQNonLin v in 
                  (MkSimulatedOp qs v' counter # MkQubit k) # (listIndex' v'' (MkQubit k))

reLinNat : (1_: Nat) -> Qubit
reLinNat Z = MkQubit Z
reLinNat (S k) = MkQubit (S k)       

lCons : (1_: Nat) -> (1_: Vect k Nat) -> Vect (S k) Nat
lCons Z [] = [Z]
lCons Z (x :: xs) = Z :: x :: xs
lCons (S k) [] = [(S k)]
lCons (S k) (x :: xs) = (S k) :: x :: xs  


export
listIndices : (1 _ : SimulatedOp n) -> (1 _ : LVect i Qubit) -> LPair (LPair (SimulatedOp n) (LVect i Qubit)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y `lCons` ys)

||| Remove an element at a given index in the vector
export
removeElem : {n : Nat} -> (1_: Vect (S n) Qubit) -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k


||| add the indices of the new qubits to the vector in the SimulatedOp
export
newQubitsPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointers 0 _ = ([] # [])
newQubitsPointers (S p) counter = 
  let (q # v) = newQubitsPointers p (S counter)
  in (MkQubit counter :: q) # (MkQubit counter :: v)


newQubits : (p : Nat) -> (counter : Nat) -> (Vect p Qubit)
newQubits 0 _= []
newQubits (S p) counter = (MkQubit counter :: (newQubits p (S counter)))

nothingToNil : (1_: ()) -> Pair (Vect 0 Qubit) ()
nothingToNil () = MkPair [] ()

nilPlus : (1_: (Vect 0 Qubit)) -> (1_: Vect i Qubit) -> LPair (Vect i Qubit) (Vect 0 Qubit)
nilPlus [] xs = (#) xs []


interface Collapsable (p : Type -> Type -> Type) where
  collapse : p a () -@ a


Collapsable LPair where
  collapse ((#) a ()) = a

public export
vectConsumed : (1_: Vect i elem) -> (1_: ()) -> (Vect i elem)
vectConsumed vect empty = collapse ((#) vect empty)

public export
Consumable (Vect i elem) where 
  consume [] = ()
  consume (x :: xs) = ()

private
applyUnitary' : {n : Nat} -> {i : Nat} -> 
   (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' v u q = 
  let (qs # v') # ind = listIndices q v
      qs2 = applyCirc ind u qs
  in (qs2 # v') where
    applyCirc : (1_: Vect i Nat) -> Unitary i -> (1 _ : SimulatedOp n) -> SimulatedOp n
    applyCirc v IdGate (MkSimulatedOp qst q counter) = (MkSimulatedOp qst (vectConsumed q (consume v)) counter)
    applyCirc v (H j g) st = 
      let vs # k = indexLTL j v 
          h = simpleTensor matrixH n k
          MkSimulatedOp qst q counter = applyCirc vs g st
      in MkSimulatedOp (h `matrixMult` qst) q counter
    applyCirc v (P p j g) st = 
      let vs # k = indexLTL j v
          ph = simpleTensor (matrixP p) n k
          MkSimulatedOp qst q counter = applyCirc vs g st
      in MkSimulatedOp (ph `matrixMult` qst) q counter
    applyCirc v (CNOT c t g) st = 
      let vcs # kc= indexLTL c v
          vts # kt= indexLTL t vcs
          cn =  tensorCNOT n kc kt
          MkSimulatedOp qst q counter = applyCirc vts g st
      in MkSimulatedOp (cn `matrixMult` qst) q counter

applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect ui)

run' : {i:Nat} -> (1_: SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> LPair (SimulatedOp n) (LVect i Qubit)
run' {i = i} simop ust = runUStateT simop ust 

private
applyUnitaryAbs' : {n : Nat} -> {i : Nat} ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitaryAbs' ust (MkSimulatedOp qs us v counter) = let (Builtin.(#) opOut lvect) = (UnitaryOp.run' (MkSimulatedOp qs us v counter) ust) in do
 (Builtin.(#) opOut lvect)

 
export
applyUnitaryAbsSimulated : {n : Nat} -> {i : Nat} ->
  (1_ : (UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ))-> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitaryAbsSimulated q = MkUST (applyUnitaryAbs' q)


export
applyC': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) ->
  (1_ : UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit))->      
    (1_ : SimulatedOp n) -> LPair (SimulatedOp n) (LVect (S i) Qubit)
applyC' (MkQubit k) qubits ust (MkSimulatedOp qsn un vn cn)=
    let ((MkSimulatedOp vacuousQS ui vacuousVi vacuousCounter) # lvect) = (UnitaryOp.run' (MkSimulatedOp (neutralIdPow i) (IdGate {n = i}) (makeNeutralVect i) i) ust) in
     let lvInt # vect = distributeDupedLVectVect qubits
         lvOut = mergeLVects lvect lvInt
         newun = UnitaryNoPrf.apply (controlled ui) un (k::vect)
       in 
        (MkSimulatedOp qsn newun vn cn) # ((MkQubit k):: lvOut)

export
applyC: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) ->
  (1_ : UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit))->      
    UStateT (SimulatedOp n) (SimulatedOp n) (LVect (S i) Qubit)
applyC ctrl qubits ust = MkUST (applyC' ctrl qubits ust)
-}
