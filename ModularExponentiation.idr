module ModularExponentiation

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import QuantumOp
import LinearTypes
--import UnitaryOp
import UStateT
import QStateT
import UnitaryLinear

import QFT
import Lemmas
--import NatRules

------------------------Quantum Modular Exponentiation------------------------

||| This file contains two implementations of QME
||| One, where the computationally most relevant set of qubits
||| for a given function is separated out throughout the implementation,
||| and one where everyting is done as usual


--------------- CLASSICAL modular inverse when we know gcd = 1 ---------------

||| An implementation of this is necessary for the below quantum implementation
||| to be feasible (for calculating a^-1 mod N as well as a^n mod N, when we
||| know gcd = 1) This is only utilized at the very end, but reference is made 
||| to it for design choices (see also Beauregard 2002)

------------------------------------------------------------------------------

toIntegerNat : Nat -> Integer
toIntegerNat Z = 0
toIntegerNat (S k) = 1 + toIntegerNat k

abs : Integer -> Integer 
abs x = if x >= 0 then x else x + (2 * (-x))

extgcd : Integer -> Integer -> Pair Integer Integer
extgcd 0 b = (0, 1)
extgcd a b = let 
                (x', y') = extgcd (b `mod` a) a
                x = y' - (b `div` a) * x'
                y = x'
              in (x, y)
    
modInverse : Nat -> Nat -> Nat
modInverse a m = fromInteger $ abs $ fst $ extgcd (toIntegerNat a) (toIntegerNat m)

---------------IN-PLACE QFT ADDER---------------

||| This expects inputs in big-endian order and
||| outputs in the same

-----------------------------------------------

addWithQFTHelp : UnitaryOp t => {k : Nat} -> {n: Nat} -> (1_ : LVect k Qubit) 
                                    -> (1_ : Qubit) -> (m : Nat) -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect 1 Qubit))
addWithQFTHelp LinearTypes.Nil b _ = pure $ [] # [b]
addWithQFTHelp (a::as) b m = do
    [a,b] <- applyUnitary [a,b] (cRm m) 
    as # b <- addWithQFTHelp as b (S m)
    pure $ (a::as) # b

addWithQFT: UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect (S i) Qubit))
addWithQFT [] b = pure $ [] # b
addWithQFT a [] impossible
addWithQFT (a :: as) (b::bs) = do
   (a :: as) # [b] <-  addWithQFTHelp (a :: as) b 1
   as # bs <-  addWithQFT as bs   
   pure $ (a :: as) # (b::bs)

export
inPlaceQFTAdder : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect (S i) Qubit))
inPlaceQFTAdder [] b = pure $ [] # b
inPlaceQFTAdder a [] impossible
inPlaceQFTAdder (a :: as) (b::bs) = do --pattern matchign requires that the lvects be of this form for some reason - idris can be strange
    qftbs <- (qftU (b::bs))
    addAs # addBs <- addWithQFT (a :: as) qftbs
    unqftbs <- (qftUInv (addBs))
    pure $ addAs # unqftbs

-------------- Alternate version, with one input vector -------------------

addWithQFTHelp2 : UnitaryOp t => {k : Nat} -> {n: Nat} -> (1_ : LVect k Qubit) 
                                    -> (1_ : Qubit) -> (m : Nat) -> UStateT (t n) (t n) ((LVect (S k) Qubit))
addWithQFTHelp2 LinearTypes.Nil b _ = pure $ [b]
addWithQFTHelp2 (a::as) b m = do
    [a,b] <- applyUnitary [a,b] (cRm m) 
    b::as <- addWithQFTHelp2 as b (S m)
    pure $ (b::a::as)

addWithQFT2: UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) ((LVect  (i + S i)  Qubit))
addWithQFT2 [] b = pure $ b
addWithQFT2 a [] impossible
addWithQFT2 {i = S k} (a :: as) (b::bs) = do
   (b::a::as) <-  addWithQFTHelp2 (a :: as) b 1
   asbs <-  addWithQFT2 as bs   
   as # bs <- splitQubitsInto k (S k) asbs --{prf =lteSiPlusi {i = k}} (k) (rewrite plusSuccRightSucc k k in asbs)
   pure $ (++) (a :: as) (b::bs)    

export
inPlaceQFTAdder2 : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) ((LVect (i + S i) Qubit))
inPlaceQFTAdder2 [] b = pure $ b
inPlaceQFTAdder2 a [] impossible
inPlaceQFTAdder2 {i = S k} (a :: as) (b::bs) = do --pattern matchign requires that the lvects be of this form for some reason - idris can be strange
    qftbs <- (qftU (b::bs))
    all <- addWithQFT2 (a :: as) qftbs
    addAs # addBs <- splitQubitsInto (S k) (S (S k)) all --{prf =lteSkS {k = k}} (S k) all
    unqftbs <- (qftUInv (addBs))
    pure $ (++) addAs unqftbs    

export
inPlaceQFTAdderUnified : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (i + S i) Qubit) -> UStateT (t n) (t n) ((LVect (i + S i) Qubit))
inPlaceQFTAdderUnified {i = Z} [b] = pure $ [b] -- since the form of the lvect is i + S i, it is at least one
inPlaceQFTAdderUnified {i = S k} (a::asbbs) = do --pattern matchign requires that the lvects be of this form for some reason - idris can be strange
    as # bs <- splitQubitsInto (S k) (S (S k)) (a::asbbs)
    qftbs <- (qftU (bs))
    all <- addWithQFT2 (as) qftbs
    addAs # addBs <- splitQubitsInto (S k) (S (S k)) all --{prf =lteSkS {k = k}} (S k) all
    unqftbs <- (qftUInv (addBs))
    pure $ (++) addAs unqftbs  

export
inPlaceQFTAdderConcat  : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) 
                                        -> UStateT (t n) (t n) (LVect (i + S i) Qubit)    
inPlaceQFTAdderConcat [] b = pure b
inPlaceQFTAdderConcat a [] impossible
inPlaceQFTAdderConcat (a :: as) (b::bs) = do --pattern matching requires that the lvects be of this form for some reason - idris can be strange
    addAs # unqftbs <- inPlaceQFTAdder (a :: as) (b::bs)
    pure (LinearTypes.(++) addAs unqftbs)

    
------------------INVERSE ADDER------------------
||| built explicitly as exercise; can be achieved by using 
||| adjointUST (inPlaceQFTAdder ... )

addWithQFTHelpInv : UnitaryOp t => {k : Nat} -> {n: Nat} -> (1_ : LVect k Qubit) 
                                    -> (1_ : Qubit) -> (m : Nat) -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect 1 Qubit))
addWithQFTHelpInv LinearTypes.Nil b _ = pure $ [] # [b]
addWithQFTHelpInv (a::as) b m = do
    as # [b] <- addWithQFTHelpInv as b (S m)
    [a,b] <- applyUnitary [a,b] (adjoint $ cRm m) 
    pure $ (a::as) # [b]

addWithQFTInv: UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect (S i) Qubit))
addWithQFTInv [] b = pure $ [] # b
addWithQFTInv a [] impossible
addWithQFTInv (a :: as) (b::bs) = do
    as # bs <-  addWithQFTInv as bs   
    (a :: as) # [b] <-  addWithQFTHelp (a :: as) b 1
    pure $ (a :: as) # (b::bs)

inPlaceQFTAdderInv : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect (S i) Qubit))
inPlaceQFTAdderInv [] b = pure $ [] # b
inPlaceQFTAdderInv a [] impossible
inPlaceQFTAdderInv (a :: as) (b::bs) = do --pattern matching requires that the lvects be of this form
    unqftbs <- (qftUInv (b::bs))    
    addAs # addBs <- addWithQFTInv (a :: as) unqftbs
    qftbs <- (qftU addBs)
    pure $ addAs # qftbs

inPlaceQFTAdderInvConcat  : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) 
                                        -> UStateT (t n) (t n) (LVect (i + S i) Qubit)    
inPlaceQFTAdderInvConcat [] b = pure b
inPlaceQFTAdderInvConcat a [] impossible
inPlaceQFTAdderInvConcat (a :: as) (b::bs) = do --pattern matching requires that the lvects be of this form for some reason - idris can be strange
    addAs # unqftbs <- inPlaceQFTAdderInv (a :: as) (b::bs)
    pure (LinearTypes.(++) addAs unqftbs)

---------------IN-PLACE MODULAR ADDER---------------       

export
inPlaceModularAdder : UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 a : LVect i Qubit) -- this is a represented in i Qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (3 + i + i)  Qubit) (LVect ((S i)) Qubit)) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceModularAdder [c1,c2] [ancilla] [] [] [q] = pure $ (c1::c2::[ancilla]) # [q]
inPlaceModularAdder [c1,c2] [ancilla] (a::as) bigNs (b::bs) = do
    (c1::c2::ass) # (bs) <- (applyControlWithSplitLVects c1 (applyControlWithSplitLVects c2 (inPlaceQFTAdder (a::as) (b::bs))))
    bigNs # bs <-  inPlaceQFTAdderInv bigNs (bs)
    (s::qibs) <- (qftUInv (bs)) -- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    [s,ancilla] <- applyCNOT s ancilla
    qftbs <- (qftUInv (s::qibs))
    ancilla::bigNs # middlebs <- applyControlWithSplitLVects ancilla (inPlaceQFTAdderInv bigNs qftbs)
    (c1::c2::ass) # (bs2) <- applyControlWithSplitLVects c1 (applyControlWithSplitLVects c2 (inPlaceQFTAdderInv ass middlebs))
    (s::qibs2) <- (qftUInv (bs2))
    [s] <- applyUnitary [s] XGate
    [s,ancilla] <- applyCNOT s ancilla
    [s] <- applyUnitary [s] XGate
    qftbs2 <- (qftU (s::qibs2))
    (c1::c2::as) # (bs) <-  applyControlWithSplitLVects c1 (applyControlWithSplitLVects c2 (inPlaceQFTAdder (ass) (qftbs2)))
    aAndN <- reCombine as bigNs
    pure $ ((++) (c1::c2::[ancilla]) aAndN) # (bs)

---------------IN-PLACE MODULAR ADDER (One Output) ---------------  
||| Alternate version that was used for checking whether split computation
||| parses correctly for complicated operations. It is far easier to 
||| do the rest by keeping some qubit lists sepatate in the output,
||| so since this was alright, only split implementations are given for the rest

inPlaceModularAdderUnified : UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 a : LVect i Qubit) -- this is a represented in i Qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) ((LVect (3 + i + S i + i) Qubit)) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceModularAdderUnified [c1,c2] [ancilla] [] [] [q] = pure $ (c1::c2::q::[ancilla])
inPlaceModularAdderUnified {i = S k} [c1,c2] [ancilla] (a::as) bigNs (b::bs) = do
    (c1::c2::asbs) <- (applyControlledAbs c1 (applyControlledAbs c2 (inPlaceQFTAdder2 (a::as) (b::bs))))
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    bigNsbs <-  adjointUST (inPlaceQFTAdder2 bigNs (bs))
    bigNs # bs <- splitQubitsInto (S k) (S (S k)) bigNsbs
    (s::qibs) <- (qftUInv (bs)) -- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    [s,ancilla] <- applyCNOT s ancilla
    qftbs <- (qftUInv (s::qibs))
    ancilla::bigNsbs <- applyControlledAbs ancilla  (adjointUST (inPlaceQFTAdder2 bigNs qftbs))
    bigNs # bs <- splitQubitsInto (S k) (S (S k)) bigNsbs
    (c1::c2::asbs) <- applyControlledAbs c1 (applyControlledAbs c2 (adjointUST (inPlaceQFTAdder2 as bs)))
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    (s::qibs) <- (qftUInv (bs))
    [s] <- applyUnitary [s] XGate
    [s,ancilla] <- applyCNOT s ancilla
    [s] <- applyUnitary [s] XGate
    qftbs <- (qftU (s::qibs))
    (c1::c2::asbs) <-  applyControlledAbs c1 (applyControlledAbs c2 (inPlaceQFTAdder2 (as) (qftbs)))
    aAndN <- reCombine asbs bigNs
    pure $ ((++) (c1::c2::[ancilla]) aAndN)

---------------IN-PLACE MODULAR MULTIPLIER---------------

||| Helper function that does the reursion on x, using each bit as control. 
allControls: UnitaryOp t => {j:Nat} -> {i: Nat} -> {n : Nat} -> {auto prf: LTE j i} -- This is somewhat superfluous, because we can handle other inputs as well it just won't make sense anyway. if we remove this there is only 1 proof required
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect j Qubit) -- this is x represented in j qubits
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + j + i + i)  Qubit) (LVect ((S i)) Qubit))
allControls [c] [ancilla] [] [] [] q = pure $ [c, ancilla] # q
allControls [_] [_] [] (x :: xs) (ns::bigNs) [] impossible -- for some reason idris wants this case
allControls [c] [ancilla] (x:: xs) [] [] [q] impossible -- because of the way b is set up, the control wont be relevant for the additiona qubit anywa; this should not happen (condition LT j i is excluded for simplicity)
allControls [c] [ancilla] (x::xs) [] [] [q] impossible -- for some reason, needs separate case
allControls [c] [ancilla] [] (a::as) (ns::bigNs) (b::bs)= do ---for some reason, idris needs the (::) operators here to recognize coverage, again...
    aAndN <- reCombine (a::as) (ns::bigNs)
    pure $ ((++) (c::[ancilla]) aAndN) # (b::bs)
allControls {prf} {j = S r} {i = S h} [c] [ancilla] (x::xs) a bigNs b = do
    (c::x::ancilla::aAndN) # b2 <- inPlaceModularAdder [c,x] [ancilla] a bigNs b
    a # bigNs <- splitQubitsAt {prf = lteSiPlusSi} (S h) aAndN -- the compiler sometimes finds this sometimes doesnt
    (c::ancilla::all) # finalb <- allControls {j = r} {i = S h} {prf = fromLteSucc $ lteSuccRight prf} [c] [ancilla] (xs) a (rewrite sym $ plusMinusLeftCancel0 h (S h) in bigNs) b2 ---ONE PROOF is necessary, the other depends on the LT condition
    pure $ (c::ancilla::x::all) # finalb 

|||Intermediaty multiplication function, output is (b+ax) mod N if c=1 else b
cMultAModN: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in i qubits 
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + i + i + i)  Qubit) (LVect ((S i)) Qubit))
cMultAModN [c] [ancilla] [] [] [] [q] = pure $ [c,ancilla] # [q]
cMultAModN [_] [_] [] [] [] [] impossible
cMultAModN [c] [ancilla] (xs) (as) (bigNs) (bs) = do
    qftb <- (qftU (bs))
    middleAll # middleB <- allControls [c] [ancilla] (xs) (as) (bigNs) qftb
    finalB <- (qftUInv middleB)
    pure $ middleAll # finalB

|||in place modular multiplication function
inPlaceModularMult: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in j qubits
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 amodinv : LVect i Qubit) -- this is a^(-1) mod N represented in i qubits. The classical algorithm for calculating this
                                                        -- from a is included above given the theoretical assurances in Beuregard
                                                        -- Note that since the content of the registers has to be prepared elsewhere, this is perfectly fine to assume
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S n) because we are actually trying to calculate (ax mod N)
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + i + i + i + i)  Qubit) (LVect (S i) Qubit)) -- this time x contains the computationally relevant bit so that is given back separately
inPlaceModularMult [c] [ancilla] [] [] [] [] [q] = pure $ [c,ancilla] # [q]
inPlaceModularMult [_] [_] [] [] [] [] [] impossible
inPlaceModularMult {i = S h} [c] [ancilla] (xs) (as) (asmodinv) (bigNs) (nils) = do
    (c::ancilla::cmulted) # (ovf::multnils) <- cMultAModN [c] [ancilla] xs as bigNs nils -- 
    xs # aAndN <- splitQubitsAt {prf = lteSiPlusPlusSi {i = h}} (S h) cmulted -- Proof 
    as # bigNs <- (splitQubitsAt {prf = plusMinusLeftCancelDeep {h = h}} (S h) aAndN) -- Proof
    c::maybexs # maybenils <- applyControlWithSplitLVects c (swapRegistersSplit xs multnils)
    (c::ancilla::all) # finalb <- (cMultAModN [c] [ancilla] (maybexs) (asmodinv) (rewrite sym $ minusminusplusplusSH {h = h} in bigNs) (ovf::maybenils)) -- Proof 
    pure $ (++) (c::ancilla::all) as # finalb

-- Now, as per Beauregard, we can classically calculate a^n mod N (see implementation above as illustration), and feed that in instead of a
-- therefore, we are done

---------------MODULAR EXPONENTIATION---------------

--This then is just calling the modular multiplication with a = a^n, and a^(-1) mod N = a^n^(-1) mod N.
-- What we do want, however, is to move the output, which is in x, into one of the output vectors by itself, as opposed to bs, this time
export
inPlaceModularExponentiation: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in j qubits
                                -> (1 an : LVect i Qubit) -- this is a^n represented in i qubits
                                -> (1 anmodinv : LVect i Qubit) -- this is a^n^(-1) mod N represented in i qubits. The classical algorithm for calculating this
                                                        -- from a is included above given the theoretical assurances in Beuregard
                                                        -- Note that since the content of the registers has to be prepared elsewhere, this is perfectly fine to assume
                                -> (1 bigN  : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S n) because we are actually trying to calculate (ax mod N)
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (3 + i + i + i + i) Qubit) (LVect (i) Qubit))
inPlaceModularExponentiation [c] [ancilla] [] [] [] [] [q] = pure $ [c,ancilla,q] # []
inPlaceModularExponentiation [_] [_] [] [] [] [] [] impossible
inPlaceModularExponentiation {i = S h} [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils) = do
    (rest) # (ovf::bs) <- inPlaceModularMult [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils)
    (c::ancilla::xs) # restrest <- splitQubitsInto {prf = plusSheq h} (S (S (S h))) (plus (plus (S h) (S h)) (S h)) rest
    all <- reCombine {i = S h} bs restrest
    finall <- reCombine {i = 3} (c::ancilla::[ovf]) (all)
    (pure $ (rewrite sym $ plusthreeSeq h in finall) # xs) -- IF the types are given carefully, then this proof is unnecessary! See below.



---------------MODULAR EXPONENTIATION No PRF---------------

inPlaceModularExponentiationNoPrf: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in j qubits
                                -> (1 an : LVect i Qubit) -- this is a^n represented in i qubits
                                -> (1 anmodinv : LVect i Qubit) -- this is a^n^(-1) mod N represented in i qubits. The classical algorithm for calculating this
                                                        -- from a is included above given the theoretical assurances in Beuregard
                                                        -- Note that since the content of the registers has to be prepared elsewhere, this is perfectly fine to assume
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S n) because we are actually trying to calculate (ax mod N)
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (S (S (S (i + (i + i + i))))) Qubit) (LVect (i) Qubit) )
inPlaceModularExponentiationNoPrf [c] [ancilla] [] [] [] [] [q] = pure $ [c,ancilla,q] # []
inPlaceModularExponentiationNoPrf [_] [_] [] [] [] [] [] impossible
inPlaceModularExponentiationNoPrf {i = S h} [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils) = do
    (rest) # (ovf::bs) <- inPlaceModularMult [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils)
    (c::ancilla::xs) # restrest <- splitQubitsInto {prf = plusSheq h} (S (S (S h))) (plus (plus (S h) (S h)) (S h)) rest
    all <- reCombine {i = S h} bs restrest
    finall <- reCombine {i = 3} (c::ancilla::[ovf]) (all)
    (pure $ (finall) # xs)


--------------- Basic encoding on natural numbers  into register of size i --------------   

data Bit : Type where 
    B0 : Bit
    B1 : Bit

partial
||| this shouldnt ever get inputs other than zero or one - idris unfortunately cannot recognize that there will be no other cases
mod2toBin : Nat -> Bit
mod2toBin any = case mod any 2 of 
    Z => B0
    (S Z) => B1


partial
||| this is in fact total, but the compiler does not recognize it
natToBinList : (num : Nat) -> List Bit
natToBinList Z = [B0]
natToBinList (S Z) = [B1]
natToBinList (S (S n)) = natToBinList (divNat (S (S n)) 2) ++ [mod2toBin (S (S n))]


||| Take i elements from a list of Bits and turn them into a vector. 
||| If the lest is empty, then we pas with zeros to the LEFT
takeiBitListtoVectPadLeft : (i: Nat) -> List Bit -> Vect i Bit
takeiBitListtoVectPadLeft Z any = []
takeiBitListtoVectPadLeft (S k) [] = rewrite sym $ lemmaplusOneRight k in takeiBitListtoVectPadLeft k [] ++ [B0] -- if the list does not contain bits, then the recovered value is zero
takeiBitListtoVectPadLeft (S k) (x::xs) = x :: (takeiBitListtoVectPadLeft  k xs)

partial
||| This is UNSAFE for convenience. Collects on the left.
natToBinIVect : (i: Nat) -> (num:Nat) -> Vect i Bit
natToBinIVect Z _ = []
natToBinIVect (S i) Z = takeiBitListtoVectPadLeft (S i) (natToBinList Z)
natToBinIVect (S i) (S n) = takeiBitListtoVectPadLeft (S i) (natToBinList (S n))

||| Takes a vector of Bins and a vector of qubits expected to be in |0>^n, and returns the unitary operation of encoding the number in the qubits
||| helper for making the below more efficient
binVectToUnitaryI : UnitaryOp t => {i:Nat} -> {n:Nat} -> (bitv: Vect i Bit) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) ( LVect i Qubit)
binVectToUnitaryI {i = Z} [] [] = pure []
binVectToUnitaryI (x::xs) [] impossible -- because i = i
binVectToUnitaryI [] (q::qs) impossible 
binVectToUnitaryI {i = S k} (x::xs) (q::qs) = case x of 
    B0 => do
         qss <- (binVectToUnitaryI xs qs)
         pure (q :: qss)
    B1 => do
        [q1] <- applyUnitary {n} {i = 1} [q] XGate
        qss <- (binVectToUnitaryI xs qs)
        pure (q1 :: qss)

partial -- because mod2ToBin is partial, and therefore natToBinList is partial, therefore natToBinIVect is partial. Could be made total.
||| Takes a Nat and a vector of qubits expected to be in |0>^n, and returns the unitary operation of encoding the number in the qubits
||| It will truncate the number if the qubits are not enoguh to contain it, otherwise it will pad
natToUnitaryI : UnitaryOp t => {i:Nat} -> {n:Nat} -> (num:Nat) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) (LVect i Qubit)
natToUnitaryI _ [] = pure []
natToUnitaryI Z (q::qs) = pure (q::qs)
natToUnitaryI {i = (S k)} (S n) (q::qs) = binVectToUnitaryI (natToBinIVect (S k) (S n)) (q::qs)

partial export
||| modular exponentiation using QuantumOp and UnitaryOp
modularExponentiationOp: QuantumOp t => UnitaryOp t => 
                                                     (1_ : LVect 1 Qubit) -- the control, comes from a different computation, 
                                                    -> (i:Nat) -> (n:Nat) -> (x : Nat) -> (a:Nat) -> (bigN: Nat)
                                                    -> QStateT (t 1) (t (2 + i + i + i + i + (S i))) ((LVect (3 + i + i + i + i + i) Qubit))
modularExponentiationOp {t = t} c i n x a bigN = let 
                                          an = power a n 
                                          anmodinv = modInverse an
                                        in
                                            do 
                                                ancilla <- newQubit {t = t} 
                                                xs0 <- newQubits {t = t} i
                                                xs <- applyUST {t = t} (natToUnitaryI x xs0)
                                                asn0 <- newQubits {t = t} i
                                                asn <- applyUST {t = t} (natToUnitaryI x asn0)
                                                asmodinv0 <- newQubits {t = t} i
                                                asmodinv <- applyUST {t = t} (natToUnitaryI x asmodinv0) 
                                                bigNs0 <- newQubits {t = t} i
                                                bigNs  <- applyUST {t = t} (natToUnitaryI x bigNs0)
                                                bsZeros <- newQubits {t = t} (S i)
                                                output <- applyUST (reCombineAbs $ inPlaceModularExponentiation c [ancilla] xs asn asmodinv bigNs bsZeros)
                                                pure (output)
                                                      