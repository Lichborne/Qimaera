       
||| Then, we have some abstract interface
interface AbstractInterface (0 t : Nat -> Type) where

    iFunction: {n : Nat} -> {i : Nat} ->
                   (1 _ : LVect i Nat) -> MyNatType i -> LStateT (t n) (t n) (LVect i Nat)

    iFunctionSingle: {n : Nat} -> (1 _ : Nat) -> LStateT (t n) (t n) Nat

    --run : (1 _ : LStateT (t m) (t m) (LVect n Nat) ) -> ((LPair (MyNatType n) (LVect n Nat))) 

interface OuterInterface (0 t : Nat -> Type) where
    ||| Apply a unitary circuit to the qubits specified by the COmbinedOp argument
    --outerFuncVec : {n : Nat} -> {i : Nat} -> (1_: LVect i Nat) -> QStateT (t n) (t n) (LVect i Nat)
    --internalOuterFunc: {n : Nat} -> {i : Nat} -> (1_: LVect i Nat) -> LStateT (t n) (t n) (LVect i Nat)
    outerFunc : {n : Nat} -> {i : Nat} -> (1_: LStateT (t n) (t n) (LVect i Nat)) -> QStateT (t n) (t n) (LVect i Nat)  
    --outerFuncPair : {n : Nat} -> {i : Nat} -> (1_: (LPair (MyNatType n) (LVect n Nat))) -> QStateT (t n) (t n) (LVect i Nat)


innerRecDummy : AbstractInterface t => (i : Nat) -> (m: Nat) -> (1 _ : LVect i Nat) -> LStateT (t m) (t m) (LVect i Nat)
innerRecDummy 0 m any = pure any
innerRecDummy (S k) m (q::qs) = pure (q::qs)   

outerRec : OuterInterface t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Nat) -> QStateT (t (m)) (t (m)) (LVect n Nat)
outerRec 0 m [] = pure []
outerRec (S k) m qs = do
        qftqs <- outerFunc (innerRecDummy {i = (S k)} {n = m} (qs))
        pure qftqs

|||we wish to write a function of the form below, such that if we get the LVect required for the iFunction, we can actually use it
recursiveFunc : AbstractInterface t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Nat) -> LStateT (t (m)) (t (m)) (LVect i Nat)
recursiveFunc {i = 0} {m = m} [] = pure []
recursiveFunc {i = 1} {m = m} [w] = do
        ww <- iFunctionSingle w
        pure $ (::) ww LinearTypes.Nil 
recursiveFunc {i = (S k)} {m = m}  (q::qs) = do 
        rec <- recursiveFunc {i = k} {m = m} (qs)
        app <- iFunction {n = m} {i = (S k)} (q::rec) (Dummy (S k))
        pure (app) 
                        
dummyFunc: Nat -> MyNatType n
dummyFunc any =  Dummy any
        
recursiveFunc2 : AbstractInterface t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Nat) -> LStateT (t (m)) (t (m)) (LVect i Nat)
recursiveFunc2 {i = 0} {m = m} [] = pure []
recursiveFunc2 {i = 1} {m = m} [w] = do
        ww <- iFunctionSingle w
        pure $ (::) ww LinearTypes.Nil 
recursiveFunc2 {i = (S k)} {m = m}  (q::qs) = do 
        rec <- recursiveFunc2 {i = k} {m = m} (qs)
        app <- iFunction {n = m} {i = (S k)} (q::rec) (dummyFunc (S k))
        pure (app) 


{-outerRecIn : OuterInterface t => (n : Nat) -> (m: Nat) -> (1 _ : LVect n Nat) -> QStateT (t (m)) (t (m)) (LVect n Nat)
outerRecIn 0 m [] = pure []
outerRecIn (S k) m qs = do
        qftqs <- outerFunc (internalOuterFunc {i = (S k)} {n = m} (qs))
pure qftqs -}

||| Then, we have some abstract interface
interface AbstractInterface2 (0 t : Nat -> Type) where

    iFunction2: {n : Nat} -> {i : Nat} ->
                   (1 _ : LVect i Nat) -> Unitary i -> LStateT (t n) (t n) (LVect i Nat)
    iFunctionSingle2: {n : Nat} -> (1 _ : Nat) -> LStateT (t n) (t n) Nat

dummyFunc2: Nat -> Unitary n
dummyFunc2 any =  IdGate

recursiveFunc3 : AbstractInterface2 t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Nat) -> LStateT (t (m)) (t (m)) (LVect i Nat)
recursiveFunc3 {i = 0} {m = m} [] = pure []
recursiveFunc3 {i = 1} {m = m} [w] = do
        ww <- iFunctionSingle2 w
        pure $ (::) ww LinearTypes.Nil 
recursiveFunc3 {i = (S k)} {m = m}  (q::qs) = do 
        rec <- recursiveFunc3 {i = k} {m = m} (qs)
        app <- iFunction2 {n = m} {i = (S k)} (q::rec) (dummyFunc2 (S k))
        pure (app) 

Rm : Nat -> Unitary 1
Rm m = PGate (2 * pi / (pow 2 (cast m)))
                

cRm : Nat -> Unitary 2
cRm m = controlled (Rm m)

cRmNRev : (n:Nat) -> Unitary n
cRmNRev 0 = IdGate
cRmNRev 1 = IdGate
cRmNRev (S (S m)) = apply (cRm (S (S m))) (tensorn (S (S m)) IdGate) [0, (S m)] 

recursiveFunc4 : AbstractInterface2 t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Nat) -> LStateT (t (m)) (t (m)) (LVect i Nat)
recursiveFunc4 {i = 0} {m = m} [] = pure []
recursiveFunc4 {i = 1} {m = m} [w] = do
        ww <- iFunctionSingle2 w
        pure $ (::) ww LinearTypes.Nil 
recursiveFunc4 {i = (S k)} {m = m}  (q::qs) = do 
        rec <- recursiveFunc4 {i = k} {m = m} (qs)
        app <- iFunction2 {n = m} {i = (S k)} (q::rec) (cRmNRev (S k))
        pure (app) 


interface COpNat (0 t : Nat -> Type) where

        ||| Apply a unitary circuit to the Qubits specified by the Vect argument
        applyUnitary : {n : Nat} -> {i : Nat} ->
                        (1 _ : LVect i Nat) -> Unitary i -> UStateT (t n) (t n) (LVect i Nat)

        ||| Apply the Hadamard gate to a single Qubit
        applyH : {n : Nat} -> (1 _ : Nat) -> UStateT (t n) (t n) Nat
        applyH q = do
        [q1] <- applyUnitary {n} {i = 1} [q] HGate 
        pure q1

        
recursiveFunc5 : COpNat t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Nat) -> UStateT (t (m)) (t (m)) (LVect i Nat)
recursiveFunc5 {i = 0} {m = m} [] = pure []
recursiveFunc5 {i = 1} {m = m} [w] = do
        ww <- applyH w
        pure $ (::) ww LinearTypes.Nil 
recursiveFunc5 {i = (S k)} {m = m}  (q::qs) = do 
        rec <- recursiveFunc5 {i = k} {m = m} (qs)
        app <- applyUnitary {n = m} {i = (S k)} (q::rec) (cRmNRev (S k))
        pure (app) 

recursiveFunc6 : UnitaryOp t => {i : Nat} -> {m: Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (m)) (t (m)) (LVect i Qubit)
recursiveFunc6 {i = 0} {m = m} [] = pure []
recursiveFunc6 {i = 1} {m = m} [w] = do
        ww <- applyH w
        pure $ (::) ww LinearTypes.Nil 
recursiveFunc6 {i = (S k)} {m = m}  (q::qs) = do 
        rec <- recursiveFunc6 {i = k} {m = m} (qs)
        app <- applyUnitary {n = m} {i = (S k)} (q::rec) (cRmNRev (S k))
        pure (app) 