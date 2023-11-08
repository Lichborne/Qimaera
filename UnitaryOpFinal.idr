module UnitaryOpFinal

import Data.Vect
import Data.Nat
import Control.Monad.State
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Lemmas
import UStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Data.Maybe
import QuantumOp

infixr 9 .
infixr 10 #

%default total

------------------------Local Lemmas --------------------------
export 
ltToLTE : {left,right:Nat} -> LTE (S left) right = LT left right 
ltToLTE = Refl

------------------------QUANTUM CIRCUITS-----------------------

private
data Unitary : Nat -> Type where
  IdGate : Unitary n
  H      : (j : Nat) -> {auto prf : LT j n} -> (1 _ : Unitary n) -> Unitary n
  P      : (p : Double) -> (j : Nat) -> {auto prf : LT j n} -> (1 _ : Unitary n) -> Unitary n
  CNOT   : (c : Nat) -> (t : Nat) -> 
            {auto prf1 : LT c n} -> {auto prf2 : LT t n} -> {auto prf3 :  Either (LT c t) (LT t c) } -> 
            (1 _ : Unitary n) -> Unitary n

-------------------------------APPLY---------------------------
|||Apply a smaller circuit of size i to a bigger one of size n
|||The vector of wires on which we apply the circuit must follow some constraints:
|||All the indices must be smaller than n, and they must be all different

public export partial -- not actually partial, just relevant proof of impossibility does not exist of other cases
apply' : {i : Nat} -> {n : Nat} -> 
        (1 _ : Unitary i) -> (1 _ : Unitary n) -> 
        (1 v : Vect i Nat) -> 
        {auto prf : (IsInjectiveT n v)} -> 
        Unitary n
apply' IdGate g2 (x::xs) = g2
apply' (H j g1) g2 (x::xs) = 
  let prf1 = indexInjectiveVect j n (x::xs) {prf} 
  in H (indexLT j (x::xs)) {prf = prf1} (apply' g1 g2 (x::xs))
apply' (P p j g1) g2 (x::xs) = 
  let prf1 = indexInjectiveVect j n (x::xs) {prf}
  in P p (indexLT j (x::xs)) {prf = prf1} (apply' g1 g2 (x::xs))
apply' {n} (CNOT c t {prf1} {prf2} {prf3} g1) g2 (x::xs) = 
  let prf4 = indexInjectiveVect c n (x::xs) {prf = prf}
      prf5 = indexInjectiveVect t n (x::xs) {prf = prf}
      prf6 = differentIndexInjectiveVect c t n {prf1 = prf3} (x::xs) {prf2 = prf} {prf3 = prf1} {prf4 = prf2}
  in CNOT (indexLT c (x::xs)) (indexLT t (x::xs)) {prf1 = prf4} {prf2 = prf5} {prf3 = prf6} (apply' g1 g2 (x::xs))

---------------------------COMPOSE-----------------------------
|||Compose 2 circuits of the same size
public export
compose : (1 _ : Unitary n) -> (1 _ : Unitary n) -> Unitary n
compose IdGate g1 = g1
compose (H j g1) g2 = H j (compose g1 g2)
compose (P p j g1) g2 = P p j (compose g1 g2)
compose (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

public export
(.) : (1 _ : Unitary n) -> (1 _ : Unitary n) -> Unitary n
(.) = compose

---------------------------ADJOINT-----------------------------
|||Find the adjoint of a circuit
public export
adjoint : Unitary n -> Unitary n
adjoint IdGate = IdGate
adjoint (H j g) = (adjoint g) . (H j IdGate)
adjoint (P p j g) = (adjoint g) . (P (-p) j IdGate)
adjoint (CNOT c t g) = (adjoint g) . (CNOT c t IdGate)


---------------------TENSOR PRODUCT----------------------------
|||Make the tensor product of two circuits
public export
tensor : {n : Nat} -> {p : Nat} -> (1 _ : Unitary n) -> ( 1 _ : Unitary p) -> Unitary (n + p)
tensor g1 g2 = 
  let p1 = allSmallerRangeVect 0 n
      p2 = isInjectiveRangeVect n p
      p3 = allSmallerPlus n p (rangeVect 0 n) p1 
      p4 = IsInjectiveSucc (allDiffRangeVect 0 n) p3
  in apply' {i = p} {n = n + p} g2 (apply {i=n} {n = n+p} g1 (IdGate {n = n+p}) (rangeVect 0 n) {prf = p4}) (rangeVect n p) {prf = p2}

private
(#) : {n : Nat} -> {p : Nat} -> (1 _ : Unitary n) -> (1 _ : Unitary p) -> Unitary (n + p)
(#) = tensor

----------------------CLASSICAL GATES--------------------------
public export
HGate : Unitary 1
HGate = H 0 IdGate

public export
PGate : Double -> Unitary 1
PGate r = P r 0 IdGate

public export
CNOTGate : Unitary 2
CNOTGate = CNOT 0 1 IdGate

public export
T : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
T j g = P (pi/4) j {prf} g

public export
TGate : Unitary 1
TGate = T 0 IdGate

public export
TAdj : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
TAdj j g = P (-pi/4) j {prf} g

public export
TAdjGate : Unitary 1
TAdjGate = TAdj 0 IdGate

public export
S : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
S j g = P (pi/2) j {prf} g

public export
SGate : Unitary 1
SGate = S 0 IdGate

public export
SAdj : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
SAdj j g = P (-pi/2) j {prf} g

public export
SAdjGate : Unitary 1
SAdjGate = SAdj 0 IdGate

public export
Z : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
Z j g = P pi j {prf} g

public export
ZGate : Unitary 1
ZGate = Z 0 IdGate

public export
X : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
X j g = H j (Z j (H j g))

public export
XGate : Unitary 1
XGate = X 0 IdGate

public export
RxGate : Double -> Unitary 1
RxGate p = HGate . PGate p . HGate

public export
RyGate : Double -> Unitary 1
RyGate p = SAdjGate . HGate . PGate (-p) . HGate . SGate

public export
RzGate : Double -> Unitary 1
RzGate p = PGate p 


---------------------CONTROLLED VERSIONS-----------------------
|||Toffoli gate
public export
toffoli : Unitary 3
toffoli = 
  let g1 = CNOT 1 2 (H 2 IdGate)
      g2 = CNOT 0 2 (TAdj 2 g1)
      g3 = CNOT 1 2 (T 2 g2)
      g4 = CNOT 0 2 (TAdj 2 g3)
      g5 = CNOT 0 1 (T 1 (H 2 (T 2 g4)))
  in CNOT 0 1 (T 0 (TAdj 1 g5))

|||Controlled Hadamard gate
public export
controlledH : Unitary 2
controlledH =
  let h1 = (IdGate {n=1}) # (SAdjGate . HGate . TGate . HGate . SGate)
      h2 = (IdGate {n=1}) # (SAdjGate . HGate . TAdjGate . HGate . SGate)
  in h1 . CNOTGate . h2

|||Controlled phase gate
public export
controlledP : Double -> Unitary 2
controlledP p = 
  let p1 = CNOT 0 1 (P (p/2) 1 IdGate)
  in CNOT 0 1 (P (-p/2) 1 p1)

|||Make the controlled version of a gate
public export
controlled : {n : Nat} -> Unitary n -> Unitary (S n)
controlled IdGate = IdGate
controlled (H j g) = 
  let p = lemmaControlledInj n j 
  in apply {i = 2} {n = S n} controlledH (controlled g) [0, S j] {prf = p}
controlled (P p j g) = 
  let p1 = lemmaControlledInj n j
  in apply {i = 2} {n = S n} (controlledP p) (controlled g) [0, S j] {prf = p1}
controlled (CNOT c t g) = 
  let p = lemmaControlledInj2 n c t
  in apply {i = 3} {n = S n} toffoli (controlled g) [0, S c, S t] {prf = p}



------------SOME USEFUL FUNCTIONS FOR CREATING GATES-----------

|||Make n tensor products of the same unitary of size 1
public export
tensorn : (n : Nat) -> Unitary 1 -> Unitary n
tensorn 0 _ = IdGate
tensorn (S k) g = g # (tensorn k g)

|||Controls on the n-1 first qubits, target on the last
public export
multipleQubitControlledNOT : (n : Nat) -> Unitary n
multipleQubitControlledNOT 0 = IdGate
multipleQubitControlledNOT 1 = IdGate
multipleQubitControlledNOT 2 = CNOT 0 1 IdGate
multipleQubitControlledNOT (S k) = controlled (multipleQubitControlledNOT k)

||| Tensor product of a Vector of Unitary operators
export
tensorMap : {n : Nat} -> {m : Nat} -> (gates : Vect n (Unitary m)) -> Unitary (n*m)
tensorMap [] = IdGate
tensorMap (gate :: gates) = gate # (tensorMap gates)

||| Tensor product of a Vector of single-qubit Unitary operators
export
tensorMapSimple : {n : Nat} -> (gates : Vect n (Unitary 1)) -> Unitary n
tensorMapSimple g = rewrite sym $ multOneRightNeutral n in tensorMap g

---------------------------------------------------------------
-- count the total number of atomic gates in a unitary circuit
export
gateCount : Unitary n -> Nat
gateCount IdGate = 0
gateCount (H j x) = S (gateCount x)
gateCount (P p j x) = S (gateCount x)
gateCount (CNOT c t x) = S (gateCount x)

--count the number of H gates in a unitary circuit
export
Hcount : Unitary n -> Nat
Hcount IdGate = 0
Hcount (H j x) = S (Hcount x)
Hcount (P p j x) = Hcount x
Hcount (CNOT c t x) = Hcount x

--count the number of P gates in a unitary circuit
export
Pcount : Unitary n -> Nat
Pcount IdGate = 0
Pcount (H j x) = Pcount x
Pcount (P p j x) = S (Pcount x)
Pcount (CNOT c t x) = Pcount x


--count the number of CNOT gates in a unitary circuit
export
CNOTcount : Unitary n -> Nat
CNOTcount IdGate = 0
CNOTcount (H j x) = CNOTcount x
CNOTcount (P p j x) = CNOTcount x
CNOTcount (CNOT c t x) = S (CNOTcount x)

----------------------------DEPTH------------------------------
|||Compute the depth of  circuit

addDepth : Nat -> (j : Nat) -> Vect n Nat -> {auto prf : LT j n} -> Vect n Nat
addDepth j 0 (x :: xs) = j :: xs
addDepth j (S k) (x :: xs) = x :: addDepth j k xs {prf = fromLteSucc prf}

findValue : (j : Nat) -> Vect n Nat -> {auto prf : LT j n} -> Nat
findValue 0 (x::xs) = x
findValue (S k) (x::xs) = findValue k xs {prf = fromLteSucc prf}

depth' : {n : Nat} -> Unitary n -> Vect n Nat
depth' IdGate = replicate n 0
depth' (H j x) =
  let v = depth' x 
      k = findValue j v
  in addDepth (S k) j v
depth' (P p j x) = 
  let v = depth' x
      k = findValue j v
  in addDepth (S k) j v
depth' (CNOT c t x) = 
  let v = depth' x 
      k = findValue c v
      m = findValue t v
  in if k < m then
              let w = addDepth (S m) c v
              in addDepth (S m) t w
     else
              let w = addDepth (S k) c v
              in addDepth (S k) t w

export
depth : {n : Nat} -> Unitary n -> Nat
depth g = 
  let v = depth' g 
  in foldl max 0 v

----------------------------SHOW-------------------------------
|||For printing the phase gate (used for show, export to Qiskit and draw in the terminal)
|||printPhase : phase -> precision -> string for pi -> String
private
printPhase : Double -> Double -> String -> String
printPhase x epsilon s =
  if x >= pi - epsilon && x <= pi + epsilon then s
  else if x >= pi/2 - epsilon && x <= pi/2 + epsilon then s ++ "/2"
  else if x >= pi/3 - epsilon && x <= pi/3 + epsilon then s ++ "/3"
  else if x >= pi/4 - epsilon && x <= pi/4 + epsilon then s ++ "/4"
  else if x >= pi/6 - epsilon && x <= pi/6 + epsilon then s ++ "/6"
  else if x >= pi/8 - epsilon && x <= pi/8 + epsilon then s ++ "/8"
  else if x >= -pi - epsilon && x <= -pi + epsilon then "-" ++ s
  else if x >= -pi/2 - epsilon && x <= -pi/2 + epsilon then "-" ++ s ++ "/2"
  else if x >= -pi/3 - epsilon && x <= -pi/3 + epsilon then "-" ++ s ++ "/3"
  else if x >= -pi/4 - epsilon && x <= -pi/4 + epsilon then "-" ++ s ++ "/4"
  else if x >= -pi/6 - epsilon && x <= -pi/6 + epsilon then "-" ++ s ++ "/6"
  else if x >= -pi/8 - epsilon && x <= -pi/8 + epsilon then "-" ++ s ++ "/8"
  else show x

public export
Show (Unitary n) where
  show IdGate = ""
  show (H j x) = "(H " ++ show j ++ ") " ++ show x 
  show (P p j x) = "(P " ++ printPhase p 0.001 "π" ++ " " ++ show j ++ ") " ++ show x
  show (CNOT c t x) = "(CNOT " ++ show c ++ " " ++ show t ++ ") " ++ show x



-----------------DRAW CIRCUITS IN THE TERMINAL-----------------

private
newWireQVect : (n : Nat) -> Vect n String
newWireQVect Z = []
newWireQVect (S k) = "" :: newWireQVect k

private
addSymbol : Nat -> Bool -> (String, String) -> Vect n String -> Vect n String
addSymbol _ _ _ [] = []
addSymbol 0 False (s1, s2) (x :: xs) = (x ++ s1) :: addSymbol 0 True  (s1, s2) xs
addSymbol 0 True  (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol 0 True  (s1, s2) xs
addSymbol (S k) _ (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol k False (s1, s2) xs

private
addSymbolCNOT : (Nat, Nat) -> Bool -> Bool -> Vect n String -> Vect n String
addSymbolCNOT _ _ _ [] = []
addSymbolCNOT (0,0)    False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, 0) True b xs
addSymbolCNOT (0, S k) False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, k) True b xs
addSymbolCNOT (0, 0)   b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (0, 0) b True xs
addSymbolCNOT (S k, 0) b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (k, 0) b True xs
addSymbolCNOT (0, 0) True True (x :: xs) = (x ++ "-----") :: addSymbolCNOT (0, 0) True True xs
addSymbolCNOT (S j, S k) _ _   (x :: xs) = (x ++ "-----") :: addSymbolCNOT (j, k) False False xs
addSymbolCNOT (0, S k) True _  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (0, k) True False xs
addSymbolCNOT (S k, 0) _ True  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (k, 0) False True xs

private
drawWirePhase : Nat -> String
drawWirePhase 0 = ""
drawWirePhase (S n) = "-" ++ drawWirePhase n

private
drawGate : {n : Nat} -> Unitary n -> Vect n String
drawGate {n} IdGate = newWireQVect n
drawGate (H i g) = addSymbol i False ("- H -", "-----") (drawGate g)
drawGate (P p i g) =
  let epsilon = 0.001 in
  if pi/4 - epsilon <= p && pi/4 + epsilon >= p
    then addSymbol i False ("- T -", "-----") (drawGate g)
  else if -pi/4 - epsilon <= p && -pi/4 + epsilon >= p
    then addSymbol i False ("- T+ -", "------") (drawGate g)
  else if pi/2 - epsilon <= p && pi/2 + epsilon >= p
    then addSymbol i False ("- S -", "-----") (drawGate g)
  else if -pi/2 - epsilon <= p && -pi/2 + epsilon >= p
    then addSymbol i False ("- S+ -", "------") (drawGate g)
  else if pi - epsilon <= p && pi + epsilon >= p
    then addSymbol i False ("- Z -", "-----") (drawGate g)
  else let s = printPhase p epsilon "π"
  in addSymbol i False ("- P(" ++ s ++ ") -", drawWirePhase (length s + 7)) (drawGate g)
drawGate (CNOT i j g) = addSymbolCNOT (i,j) False False (drawGate g)


private
drawVect : Vect n String -> String
drawVect [] = ""
drawVect (x :: xs) = x ++ "\n" ++ drawVect xs

|||Draw a circuit in the terminal
public export
draw : {n : Nat} ->  Unitary n -> IO ()
draw g =
  let vs1 = drawGate {n} g in
  let s = drawVect vs1 in
  putStrLn s



--------------------------EXPORT TO QISKIT---------------------

private
unitarytoQiskit : Unitary n -> String
unitarytoQiskit IdGate = ""
unitarytoQiskit (H i g) = unitarytoQiskit g ++  "qc.h(qr[" ++ show i ++ "])\n"
unitarytoQiskit (P p i g) = unitarytoQiskit g ++ "qc.p(" ++ printPhase p 0.001 "np.pi" ++ ", qr[" ++ show i ++ "])\n" 
unitarytoQiskit (CNOT c t g) = unitarytoQiskit g ++ "qc.cx(qr[" ++ show c ++ "], qr[" ++ show t ++ "])\n" 


private
toQiskit : {n : Nat} -> Unitary n -> String
toQiskit g =
  let s = unitarytoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show n ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nqc.draw('mpl')")

|||Export a circuit to Qiskit code
public export
exportToQiskit : {n : Nat} -> String -> Unitary n -> IO ()
exportToQiskit str g =
  let s = toQiskit g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()







||| The UnitaryOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Wires it contains.
export
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Wires specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Wire) -> Unitary i -> UStateT (t n) (t n) (LVect i Wire)

  ||| Apply the Hadamard gate to a single Wire
  applyH : {n : Nat} -> (1 _ : Wire) -> UStateT (t n) (t n) Wire
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure q1

  ||| Apply a P gate to a single Wire
  applyP : {n : Nat} -> Double -> (1 _ : Wire) -> UStateT (t n) (t n) Wire
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure q1

  ||| Apply the CNOT gate to a pair of Wires
  applyCNOT : {n : Nat} -> (1 _ : Wire) -> (1 _ : Wire) -> UStateT (t n) (t n) (LPair Wire Wire)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1 # q2)

  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 Wires) and measure 'n' Wires in the process
  run : (1 _ : t 0) -> (1 _ : UStateT (t 0) (t n) (LVect n Wire) ) -> R (LPair (t n) (LVect n Wire))
  run u0 ust = runUStateT u0 ust

{-
export
data UnitaryUse : Nat -> Type where
  MkUnitaryUse : {n : Nat} -> (v: Vect n Wire) -> IsInjectiveT n (natReV v) -> Unitary n -> Nat -> UnitaryUse n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------


||| Find an element in a list : used to find the relevant Wire
private
listIndex' : {n : Nat} -> (v:Vect n Wire) -> Wire -> Nat
listIndex' [] _ = 0
listIndex' (MkWire x :: xs) (MkWire k) = if x == k then 0 else S (listIndex' xs (MkWire k))

private
listIndex : (1 _ : UnitaryUse n) -> (1 _ : Wire) -> LFstPair (LPair (UnitaryUse n) Wire) Nat
listIndex (MkUnitaryUse v prf un c) (MkWire k) = ((MkUnitaryUse v prf un c) # MkWire k) # (listIndex' v (MkWire k))

private 
listIndices : (1 _ : UnitaryUse n) -> (1 _ : LVect i Wire) -> LFstPair (LPair (UnitaryUse n) (LVect i Wire)) (DPair (Vect i Nat) (\v => IsInjectiveT i v))
listIndices qs [] = (qs # []) # (MkDPair [] (IsInjectiveSucc AllDiffNil ASNil))
listIndices (MkUnitaryUse v prf un c) (x :: xs) = 
  let (qs' # x') # y = listIndex qs x
      (qs2 # xs') # ys = listIndices qs' xs
  in (qs2 # (x' :: xs')) # (y :: ys)

||| Remove an element at a given index in the vector
private 
removeElem : {n : Nat} -> Vect (S n) Wire -> Nat -> Vect n Wire
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k

||| add the indices of the new Wires to the vector in the SimulatedOp
private 
newWiresPointers : (p : Nat) -> (counter : Nat) -> (m:Nat) -> (w: Vect m Wire) -> (inj: IsInjectiveT m (natReV w)) ->
    LFstPair (LVect p Wire) (DPair (Vect p Wire) (\v => IsInjectiveT (m+p) (natReV (w ++ v))))
newWiresPointers 0 c m v prf = ([] # (MkDPair [] (believe_me () $ prf)))
newWiresPointers (S p) counter m w prf = 
  let (q # (MkDPair v injsofar)) = newWiresPointers p (S counter) m w prf
  in (MkWire counter :: q) #  (MkDPair (MkWire counter :: v)  (believe_me()))

private
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Wire) -> Unitary i -> (1 _ : UnitaryUse n) -> R (LPair (UnitaryUse n) (LVect i Wire))
applyUnitary' v u (MkUnitaryUse vs prf un counter) = 
    let (us1 # v') # ind = listIndices (MkUnitaryUse vs prf un counter) v 
        us2 = applyCirc ind u us1 (believe_me ())
    in pure1 (us2 # v') where
      applyCirc : (v: Vect i Nat) -> Unitary i -> (1 _ : UnitaryUse n) -> (inj: IsInjectiveT n v) -> UnitaryUse n
      applyCirc v IdGate ust inj = ust
      applyCirc v gate (MkUnitaryUse vs prf un counter) inj= 
        --let MkUnitaryUse vs un counter = applyCirc v g st in
        MkUnitaryUse vs prf (apply gate un v {prf = inj}) counter
      
||| Add new Wires to a Quantum State
export
newWiresUse : (p : Nat) -> UStateT (UnitaryUse n) (UnitaryUse (n+p)) (LVect p Wire)
newWiresUse p = MkUST (newWires' p) where
  newWires' : (q : Nat) -> (1 _ : UnitaryUse m) -> R (LPair (UnitaryUse (m + q)) (LVect q Wire))
  newWires' q (MkUnitaryUse v prf un counter) =
    let (wires # (MkDPair v' inj)) = newWiresPointers q counter m v prf
    in pure1 (MkUnitaryUse (v ++ v') (inj) (tensor un (IdGate)) (counter + q) # wires)


||| Apply a unitary circuit to a UnitaryUse
export
applyUnitaryUse : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Wire) -> Unitary i -> UStateT (UnitaryUse n) (UnitaryUse n) (LVect i Wire)
applyUnitaryUse q u = MkUST (applyUnitary' q u)
  
export
UnitaryOp UnitaryUse where
  newWires    = newWiresUse
  applyUnitary = applyUnitaryUse
  

||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))


||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

cRmN : (n:Nat) -> Unitary n
cRmN 0 = IdGate
cRmN 1 = IdGate
cRmN (S (S k)) = apply (cRm (S (S k))) (tensorn (S (S k)) IdGate) [S k, 0]

cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S k)) = apply (cRm (S (S k))) (tensorn (S (S k)) IdGate) [0, (S k)]

fExp : (1 _ : (1 _ : Unitary n) -> R (LPair (Unitary (S n)) (LVect (S n) Wire))) -> ((1 _ : Unitary (S n))-> R (LPair (Unitary (S n)) (LVect (S n) Wire)))
fExp g = ?what

pushup:{n:Nat} -> (1 _ : UStateT (Unitary n) (Unitary (S n)) (LVect (S n) Wire)) -> UStateT (Unitary (S n)) (Unitary (S n)) (LVect (S n) Wire)
pushup (MkUST f) = MkUST (\x => (fExp f) x)

natRe : (1 _ : Wire) -> Nat
natRe (MkWire Z) = Z
natRe (MkWire (S k)) = S k

qftRecRev : UnitaryOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Wire) -> UStateT (t (n+m)) (t (n+m)) (LVect n Wire)
qftRecRev 0 m [] = pure []
qftRecRev 1 m [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecRev (S (S k)) m (q::qs) = rewrite plusSuccRightSucc k m in do
        recwires <- qftRecRev (S k) (S m) (qs)
        app <- applyUnitary (q::recwires) (cRmNRev (S (S k)))
        pure (app)

qftRecTry : UnitaryOp t =>  UStateT (t 0) (t 5) (LVect 5 Wire)
qftRecTry = do
  ws <- newWires 5
  app <- qftRecRev 5 0 ws
  pure app


qftFinal = qftRecTry {t = UnitaryUse}

-}
export
data UnitaryUse : Nat -> Type where
  MkUnitaryUse : {n : Nat} -> (v: Vect n Wire) -> Unitary n -> Nat -> UnitaryUse n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------

private
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Wire) -> Unitary i -> (1 _ : UnitaryUse n) -> R (LPair (UnitaryUse n) (LVect i Wire))
applyUnitary' v u us = 
    let (us1 # v') # ind = listIndices us v 
        us2 = applyCirc ind u us1
    in pure1 (us2 # v') where
      applyCirc : Vect i Nat -> Unitary i -> (1 _ : UnitaryUse n) -> UnitaryUse n
      applyCirc v IdGate ust = ust
      applyCirc v gate (MkUnitaryUse vs un counter) = 
        --let MkUnitaryUse vs un counter = applyCirc v g st in
        MkUnitaryUse vs (apply gate un v {prf = believe_me ()}) counter
      
||| Add new Wires to a Quantum State
export
newWiresUse : (p : Nat) -> UStateT (UnitaryUse n) (UnitaryUse (n+p)) (LVect p Wire)
newWiresUse p = MkUST (newWires' p) where
  newWires' : (q : Nat) -> (1 _ : UnitaryUse m) -> R (LPair (UnitaryUse (m + q)) (LVect q Wire))
  newWires' q (MkUnitaryUse v un counter) =
    let (wires # v') = newWiresPointers q counter
    in pure1 (MkUnitaryUse (v ++ v') (tensor un (IdGate)) (counter + q) # wires)


||| Apply a unitary circuit to a UnitaryUse
export
applyUnitaryUse : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Wire) -> Unitary i -> UStateT (UnitaryUse n) (UnitaryUse n) (LVect i Wire)
applyUnitaryUse q u = MkUST (applyUnitary' q u)
  
export
UnitaryOp UnitaryUse where
  newWires    = newWiresUse
  applyUnitary = applyUnitaryUse
  

||| Phase gate with phase 2 pi / (2^m)
Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))


||| Controlled phase gate with phase 2 pi / (2^m)
cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

cRmN : (n:Nat) -> Unitary n
cRmN 0 = IdGate
cRmN 1 = IdGate
cRmN (S (S k)) = apply (cRm (S (S k))) (tensorn (S (S k)) IdGate) [S k, 0]

cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S k)) = apply (cRm (S (S k))) (tensorn (S (S k)) IdGate) [0, (S k)]

fExp : (1 _ : (1 _ : Unitary n) -> R (LPair (Unitary (S n)) (LVect (S n) Wire))) -> ((1 _ : Unitary (S n))-> R (LPair (Unitary (S n)) (LVect (S n) Wire)))
fExp g = ?what

pushup:{n:Nat} -> (1 _ : UStateT (Unitary n) (Unitary (S n)) (LVect (S n) Wire)) -> UStateT (Unitary (S n)) (Unitary (S n)) (LVect (S n) Wire)
pushup (MkUST f) = MkUST (\x => (fExp f) x)

natRe : (1 _ : Wire) -> Nat
natRe (MkWire Z) = Z
natRe (MkWire (S k)) = S k

qftRecRev : UnitaryOp t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Wire) -> UStateT (t (n+m)) (t (n+m)) (LVect n Wire)
qftRecRev 0 m [] = pure []
qftRecRev 1 m [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecRev (S (S k)) m (q::qs) = rewrite plusSuccRightSucc k m in do
        recwires <- qftRecRev (S k) (S m) (qs)
        app <- applyUnitary (q::recwires) (cRmNRev (S (S k)))
        pure (app)

qftRecTry : UnitaryOp t =>  UStateT (t 0) (t 5) (LVect 5 Wire)
qftRecTry = do
  ws <- newWires 5
  app <- qftRecRev 5 0 ws
  pure app

  
qftFinal = qftRecTry {t = UnitaryUse}

{-}
qftUnitarySafe : (n : Nat) -> (1 _ : Vect n Wire) -> Unitary n
qftUnitarySafe 0 [] = IdGate
qftUnitarySafe 1 [w] = HGate
qftUnitarySafe (S (S k)) (qs) = let t1 = tensor (qftUnitarySafe (S k) (takeOneV1 (qs))) IdGate in 
                                    rewrite sym $ lemmaplusOneRight k in
                                      apply (cRm (S (S k))) t1 [S k, 0]

qftRec : UnitaryOp Unitary => (n : Nat) -> (1 _ : Vect n Wire) -> UStateT (Unitary n) (Unitary n) (Vect n Wire)
qftRec Z [] = pure []
qftRec (S m) (w::ws) = do
  q <- applyUnitary (w::ws) (qftUnitarySafe (S m) (w::ws))
  pure q

qftR : UnitaryOp Unitary => (n : Nat) -> UStateT (Unitary 0) (Unitary n) (Vect n Wire)
qftR 0 = pure []
qftR (S k) = do
  (w::ws) <- newWires (S k)
  out <- qftRec (S k) (w::ws)
  pure out


------------------------------------

qftRecRev2 : UnitaryOp Unitary => (n : Nat) -> UStateT (Unitary 0) (Unitary n) (LVect n Wire)
qftRecRev2 0 = pure []
qftRecRev2 1 = do
        w <- newWire
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecRev2 (S (S k)) = do
  recwires  <- qftRecRev2 (S k)
  app <- applyUnitaryL recwires (cRmNRev (S k))
  pure app


  qftRec : (n : Nat) -> Unitary n
  qftRec 0 = IdGate
  qftRec 1 = HGate
  qftRec (S (S k)) = 
    let t1 = (qftRec (S k)) # IdGate
    in rewrite sym $ lemmaplusOneRight k in apply (cRm (S (S k))) t1 [S k, 0] 

qftRecRev : UnitaryOp Unitary => (n : Nat) -> (1 _ : LVect n Wire) -> UStateT (Unitary n) (Unitary n) (LVect n Wire)
qftRecRev 0 [] = pure []
qftRecRev 1 [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRecRev (S (S k)) (q::qs) = do
  qftRecRev (S k) (qs)
  applyUnitary (q::recwires) (cRmNRev (S (S k))) >>= (\app => pure (app))
{
qftRec : UnitaryOp Unitary => (n : Nat) -> (1 _ : LVect n Wire) -> UStateT (Unitary n) (Unitary n) (LVect n Wire)
qftRec 0 [] = pure []
qftRec 1 [w] = do
        wh <- applyH w
        pure $ (::) wh LinearTypes.Nil 
qftRec (S (S k)) (q::qs) = rewrite sym $ lemmaplusOneRight k in do
        recwires <- qftRec (S k) (takeNmOneL (q::qs))
        plus <- newWire
        applied <- applyUnitary (recwires++[plus]) (cRmN (S (S k)))
        pure applied
      
qftRec0 : UnitaryOp Unitary => UStateT (Unitary 0) (Unitary 0) (LVect 0 Wire)
qftRec0 = pure []


qftRec1 : UnitaryOp Unitary => UStateT (Unitary 1) (Unitary 2) (LVect 1 Wire)
qftRec1 = do
    w <- newWire
    wh <- applyH w
    pure $ (::) wh LinearTypes.Nil 

qftRecSSk : UnitaryOp Unitary => (n : Nat) -> UStateT (Unitary n) (Unitary n) (LVect n Wire)
qftRecSSk (S (S k)) = rewrite sym $ lemmaplusOneRight k in do
        wires <- qftRecSSk (S k)
        applied <- applyUnitary wires (cRm (S (S k)))
        pure applied


-}