module UnitaryFinal

import Data.Vect
import Data.Nat
import Control.Monad.State
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Lemmas
import UnitaryLinear
import UStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Data.Maybe
import Language.Reflection

infixr 11 ~~
infixr 12 -<>-

-----Auxiliaries ------
export
data Wire : Type where
  MkWire : (n : Nat) -> Wire

consLinW : (1 _ : Wire) -> (1 _ : Vect n Wire) -> Vect (S n) Wire
consLinW (MkWire Z) [] = [(MkWire Z)]
consLinW (MkWire Z) (x :: xs) = (MkWire Z) :: x :: xs
consLinW ((MkWire (S k))) [] = [MkWire (S k)]
consLinW (MkWire (S k)) (x :: xs) = (MkWire (S k)) :: x :: xs

nilToLNIL : (1 _ : Vect 0 Wire) -> LVect 0 Wire
nilToLNIL [] = []

toVectW : {n:Nat} -> (1 _ : LVect n Wire) -> Vect n Wire
toVectW [] = []
toVectW (x :: xs) = x `consLinW` (toVectW xs)

consWV : (1 _ : Wire) -> (1 _ : Vect n Wire) -> LVect (S n) Wire
consWV (MkWire Z) [] = [(MkWire Z)]
consWV (MkWire Z) (x :: xs) = (MkWire Z) :: (consWV x xs)
consWV ((MkWire (S k))) [] = [MkWire (S k)]
consWV (MkWire (S k)) (x :: xs) = (MkWire (S k)) :: (consWV x xs)

toLVectW : (1 _ : Vect n Wire) -> LVect n Wire
toLVectW [] = []
toLVectW (x :: xs) = x `consWV` xs

takeOneV1 : (1 _ : Vect (S n) Wire) -> (Vect n Wire)
takeOneV1 [q] = []
takeOneV1 (q::qs::qss) = q :: takeOneV1 (qs::qss)

duplicateVect : {n:Nat} -> (1 _ :  (Vect n Wire)) -> LPair (Vect n Wire) (Vect n Wire)
duplicateVect [] = [] # []
duplicateVect {n = S k} (x::xs) = (x::xs) # (x::xs)

natReV : (1 _ : Vect n Wire) -> Vect n Nat
natReV [] = []
natReV (MkWire any::ws) = any :: (natReV ws)

--duplicateVectN : {n:Nat} -> (1 _ :  (Vect n Nat)) -> Pair (Vect n Nat) (Vect n Nat)
--duplicateVectN [] = MkPair [] []
--duplicateVectN (x::xs) = MkPair (x::(fst $ duplicateVect xs)) (x::(snd $ duplicateVect xs))

takeNmOneL : (1 _ : LVect (S n) Wire) -> (LVect n Wire)
takeNmOneL [q] = nilToLNIL $ takeOneV1 (toVectW [q]) 
takeNmOneL (q::qs::qss) = q :: takeNmOneL (qs::qss)
-----------------------------------------------------

vectExp :{n:Nat} -> Vect n Nat -> (p:Nat)  -> Vect (n+p) Nat
vectExp v p= v ++ (rangeVect n p)

public export
(~~) : {n : Nat} -> Vect n Nat -> (p:Nat) -> Vect (n+p) Nat
(~~) v p = vectExp v p

public export 
prfExp : {n:Nat} -> (prf: IsInjectiveT n v) -> (p:Nat) -> (IsInjectiveT (n+p) (v ~~ p))
prfExp (IsInjectiveSucc all sm) p = believe_me ()

public export
(-<>-) : {n : Nat} -> (prf: IsInjectiveT n v)  -> (p:Nat) -> (IsInjectiveT (n+p) (v ~~ p))
(-<>-) = prfExp

||| The UnitaryOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of Wires it contains.
export
interface UnitaryOp (0 t : (n: Nat) -> (v: Vect n Nat) -> (prf: IsInjectiveT n v) -> Type) where

  ||| Prepare 'p' new Wires in state |00...0>
  newWires : (p : Nat) -> UStateT (t n v prf) (t (n+p) (v ~~ p) (prf -<>- p)) (LVect p Wire)
  newWires Z     = rewrite plusZeroRightNeutral n in (believe_me () $ pure LinearTypes.Nil)
  newWires (S k) = rewrite lemmaPlusSRight n k in do
    q <- newWire
    qs <- newWires k
    pure $ (LinearTypes.(::) q qs)

  ||| Prepare a single new Wire in state |0>
  newWire : UStateT (t n v prf) (t (S n) (v ~~ 1) (prf -<>- 1)) Wire
  newWire = rewrite sym $ lemmaplusOneRight n in do
    [q] <- newWires 1
    pure q
{-}
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

export
data UnitaryUse : Nat -> Type where
  MkUnitaryUse : {n : Nat} -> (v: Vect n Wire) -> IsInjectiveT n (natReV v) -> Unitary n -> Nat -> UnitaryUse n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------


||| Find an element in a list : used to find the wire of a Wire
private
listIndex' : {n : Nat} -> (v:Vect n Wire) -> Wire -> Nat
listIndex' [] _ = 0
listIndex' (MkWire x :: xs) (MkWire k) = if x == k then 0 else S (listIndex' xs (MkWire k))

private
listIndex : (1 _ : UnitaryUse n) -> (1 _ : Wire) -> LFstPair (LPair (UnitaryUse n) Wire) Nat
listIndex (MkUnitaryUse v prf un c) (MkWire k) = ((MkUnitaryUse v prf un c) # MkWire k) # (listIndex' v (MkWire k))

private 
listIndices : (1 _ : UnitaryUse n) -> (1 _ : LVect i Wire) -> LFstPair (LPair (UnitaryUse n) (LVect i Wire)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
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
newWiresPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Wire) (Vect p Wire)
newWiresPointers 0 _ = ([] # [])
newWiresPointers (S p) counter = 
  let (q # v) = newWiresPointers p (S counter)
  in (MkWire counter :: q) #  (MkWire counter :: v)


private
applyUnitary' : {n : Nat} -> {i : Nat} ->
                (1 _ : LVect i Wire) -> Unitary i -> (1 _ : UnitaryUse n) -> R (LPair (UnitaryUse n) (LVect i Wire))
applyUnitary' v u (MkUnitaryUse vs prf un counter) = 
    let (us1 # v') # ind = listIndices (MkUnitaryUse vs prf un counter) v 
        us2 = applyCirc ind u us1 prf
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
    let (wires # v') = newWiresPointers q counter
    in pure1 (MkUnitaryUse (v ++ v') prf (tensor un (IdGate)) (counter + q) # wires)


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
export
data UnitaryUse : Nat -> Type where
  MkUnitaryUse : {n : Nat} -> (v: Vect n Wire) -> Unitary n -> Nat -> UnitaryUse n

------ SIMULATION : AUXILIARY (PRIVATE) FUNCTIONS ------


||| Find an element in a list : used to find the wire of a Wire
private
listIndex' : {n : Nat} -> Vect n Wire -> Wire -> Nat
listIndex' [] _ = 0
listIndex' (MkWire x :: xs) (MkWire k) = if x == k then 0 else S (listIndex' xs (MkWire k))

private
listIndex : (1 _ : UnitaryUse n) -> (1 _ : Wire) -> LFstPair (LPair (UnitaryUse n) Wire) Nat
listIndex (MkUnitaryUse v un c) (MkWire k) = ((MkUnitaryUse v un c) # MkWire k) # (listIndex' v (MkWire k))

private 
listIndices : (1 _ : UnitaryUse n) -> (1 _ : LVect i Wire) -> LFstPair (LPair (UnitaryUse n) (LVect i Wire)) (Vect i Nat)
listIndices qs [] = (qs # []) # []
listIndices qs (x :: xs) = 
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
newWiresPointers : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Wire) (Vect p Wire)
newWiresPointers 0 _ = ([] # [])
newWiresPointers (S p) counter = 
  let (q # v) = newWiresPointers p (S counter)
  in (MkWire counter :: q) #  (MkWire counter :: v)


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
{-}
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

