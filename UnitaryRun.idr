import Data.Nat
import Lemmas
import LinearTypes
import UnitaryLinear
import UStateT



idUp :  {m:Nat} -> (1 _ : Unitary m) -> (q : Nat) -> Unitary (m + q)
idUp um Z = rewrite plusZeroRightNeutral m in um
idUp um (S k) = um # (IdGate {n = (S k)})

export
newQubitsUST : {n:Nat} -> (p : Nat) -> UStateT (Unitary n) (Unitary (n+p)) (LVect p Qubit)
newQubitsUST p = MkUST (newQubits' p) where
  newQubits' : {m:Nat} -> (q : Nat) -> (1 _ : Unitary m) ->(LPair (Unitary (m + q)) (LVect q Qubit))
  newQubits' {m} q un = 
    let (qubits # v') = newQubitsPointersNoCount q (mkQubitV 0 m)
    in (idUp un q # qubits)


public export
interface RunUnitaryOp (0 t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  newQubits : (p : Nat) -> UStateT (t n) (t (n+p)) (LVect p Qubit)
  newQubits Z     = rewrite plusZeroRightNeutral n in pure []
  newQubits (S k) = rewrite lemmaPlusSRight n k in do
    q <- newQubit
    qs <- newQubits k
    pure (q :: qs)

  ||| Prepare a single new qubit in state |0>
  newQubit : UStateT (t n) (t (S n)) Qubit
  newQubit = rewrite sym $ lemmaplusOneRight n in do
    [q] <- newQubits 1
    pure q
  
  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUST : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LVect i Qubit)) -> UStateT (t n) (t n) (LVect i Qubit)
     
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  runUST : {n:Nat} -> UStateT (t 0) (t n) (LVect i Qubit) -> (t n)



||| Helper for Unitay implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTR': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitay n) (LVect i Qubit))      
                   -> (1 _ : Unitay n) -> LPair (Unitay n) (LVect i Qubit)
applyUSTR' ust (MkUnitay qs un v counter) = 
  let (un # lvect) = runUStateT un ust in
        let unew = compose unew un in
          do ((MkUnitay qs unew vnew counter) # (lvect))

||| Unitay implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedR : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitay n) (Unitay n) (LVect i Qubit))      
                   -> QStateT (Unitay n) (Unitay n) (LVect i  Qubit)
applyUSTSimulatedR ust = MkQST (applyUSTR' ust )

      