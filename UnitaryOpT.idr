module UnitaryOpT

import Data.Vect
import Data.Nat
import Control.Monad.State
import Decidable.Equality
import System.File
import Injection
import Matrix
import Complex
import Lemmas
import Unitary
import UState
--import QStateT
import Control.Linear.LIO
import LinearTypes
import Data.String
import Data.Maybe
--import Unitary
||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.

unpack : String -> List Char
unpack s with (strM s)
  unpack ""             | StrNil = []
  unpack (strCons x xs) | (StrCons x xs) = x :: assert_total (UnitaryOpT.unpack xs)

maybeToList : Maybe a -> List a
maybeToList  Nothing   = []
maybeToList  (Just x)  = [x]

getStr : IO (List Char)
getStr = do
    i <- getLine
    pure (UnitaryOpT.unpack i)

maybeIntToNat : Maybe Integer -> Maybe Nat
maybeIntToNat a = do
  num <- a
  pure (fromInteger num)

getNum' : IO (Maybe Nat)
getNum' = do
    i <- getStr 
    pure $ maybeIntToNat (parseNumWithoutSign i 0)

sortOut : (n:Nat) -> (v:Vect i Nat) -> (p:Nat ** Vect p Nat)
sortOut n v = filter (\x => x < n) (snd (nub v))

allSInputVect : (n:Nat) -> (v:Vect i Nat) -> Maybe (AllSmallerT v n)
allSInputVect _ [] = Just ASNil
allSInputVect n (x::xs) = case isLT x n of
  Yes prf1 => do
    pre <- (allSInputVect n xs)
    pure (ASSucc prf1 pre)
  No prf2 => Nothing

isDiffVect : (m:Nat) -> (v:Vect i Nat) -> Maybe (IsDifferentT m v)
isDiffVect _ [] = Just IsDiffNil
isDiffVect m (x::xs) = case isLT x m of
  Yes prf1 => do
    pre <- (isDiffVect m xs)
    pure (IsDiffSucc (Right prf1) pre)
  No prf2 => case isLT m x of
    Yes prf3 => do
      pre <- (isDiffVect m xs)
      pure (IsDiffSucc (Left prf3) pre)
    No prf4 => Nothing

allDiffVect : (v:Vect i Nat) -> Maybe (AllDifferentT v)
allDiffVect [] = Just AllDiffNil
allDiffVect (x::xs) = case isDiffVect x xs of
                      (Just a) => do
                        pre <- (allDiffVect xs)
                        pure (AllDiffSucc a pre)
                      Nothing => Nothing

maybeIsInjective : (n:Nat) -> (v:Vect i Nat) -> Maybe (IsInjectiveT n v)
maybeIsInjective n v = do
  allS <- allSInputVect n v
  allD <- allDiffVect v
  pure $ IsInjectiveSucc allD allS

sortOutTest : {i: Nat} -> (n:Nat) -> (v:Vect i Nat) -> Bool
sortOutTest {i} n v = fst (sortOut n v) == i

getVec : (iLeft:Nat) -> IO (Vect iLeft (Maybe Nat))
getVec Z = do
    pure []
getVec (S k) = do
    elem <- getNum'
    vs <- getVec k
    pure (Vect.(::) elem vs)

vectMaybeToList : (Vect i (Maybe Nat)) -> (Vect i (List Nat))
vectMaybeToList [] = []
vectMaybeToList (v::vs) =  Vect.(::) (maybeToList v) (vectMaybeToList vs) 

{-natSingletonsToNat : (p:Nat ** Vect p (List Nat)) -> (p:Nat ** Vect p Nat)
natSingletonsToNat (MkDPair a vs) = MkDPair a (map List.head vs)-}

--an empy list will not be passed to this locally, because we filter for them right before (extracting the proof is a bit too annoying here for now)
private 
localSingletonToNat: List Nat -> Nat
localSingletonToNat [] = 0
localSingletonToNat (x::xs) = x


vectMaybeToNat : (Vect i (Maybe Nat)) -> (p:Nat ** Vect p (Nat))
vectMaybeToNat vs = let pair = (filter (\x => x == []) (vectMaybeToList vs)) in
                      MkDPair (fst pair) (map localSingletonToNat (snd pair))


applyURepeatX : (i:Nat) -> (n:Nat) -> (tries:Nat) -> IO (Pair Bool (p:Nat ** Vect p (Nat)))
applyURepeatX (i) (n) Z = do
                    leVectorUwU <- getVec i
                    case (fst (vectMaybeToNat leVectorUwU) == i) of 
                      True => (pure (MkPair True (vectMaybeToNat leVectorUwU)))
                      False => pure (MkPair False (vectMaybeToNat leVectorUwU))
applyURepeatX (i) (n) (S k) = do
                    leVectorUwU <- getVec i
                    case (fst (vectMaybeToNat leVectorUwU) == i) of 
                      True =>  pure (MkPair True (vectMaybeToNat leVectorUwU))
                      False => applyURepeatX i n k

applyUSep : {i:Nat} -> {n:Nat} -> Unitary i -> (v : Vect i Nat) -> Unitary n -> IO (Unitary n)
applyUSep {i} {n} ui v un = case (maybeIsInjective n v) of
                              (Just a) => (do
                                putStrLn ("Inputs are of the correct form, proceeding")
                                Prelude.pure (Unitary.apply {i = i} {n = n} ui un v {prf = a}))
                              Nothing => do
                                putStrLn ("Unfortunately, the vector of wires provided cannot be used, because it is not of the right length, or contains indeces which do not belong to an existing wire. Please try again.")
                                pairpair <- applyURepeatX i n 3
                                case decEq ((snd pairpair).fst) i of
                                  Yes prf1 => pure $ (Unitary.apply {i = i} {n = n} ui un (rewrite (sym prf1) in Builtin.DPair.DPair.snd (snd (pairpair))) {prf = ?whatnow})
                                  No prf2 => pure un

applyU : {i:Nat} -> {n:Nat} -> Unitary i -> (v : Vect i Nat) -> UState (Unitary n) (Unitary n) (Unitary n)
applyU {i} {n} ui v = case (maybeIsInjective n v) of
                        (Just a) => (do
                          un <- MkUS (\u => pure (MkPair u u))
                          a <- pure (Unitary.apply {i = i} {n = n} ui un v {prf = a})
                          pure a)
                        Nothing => MkUS (\u => pure (MkPair u u))

applyUF : {i:Nat} -> {n:Nat} -> Unitary i -> (v : Vect i Nat) -> UState (Unitary n) (Unitary n) (Unitary n)
applyUF {i} {n} ui v = case (maybeIsInjective n v) of
                      (Just a)=> (do
                        un <- MkUS (\u => pure (MkPair u u))
                        pure (Unitary.apply {i = i} {n = n} ui un v {prf = a}))
                      Nothing => MkUS (\u => do
                        putStrLn "Vector input incorrect, state of computation unchanged"
                        pure (MkPair u u))


                            --putStrLn ("Inputs are of the correct form, proceeding")    
                            

{-export
applyU : {i:Nat} -> {n:Nat} -> Unitary i -> (v : Vect i Nat) -> UState (Unitary n) (Unitary n) (Unitary n)
applyU {i} {n} ui v = case (sortOutTest n v) of
                        True => (do
                          putStrLn ("Inputs are of the correct form, proceeding")
                          do
                            un <- get
                            Prelude.pure (Unitary.apply {i = i} {n = n} ui un v {prf = ?what2}))
                        False => do
                          putStrLn ("Unfortunately, the vector of wires provided cannot be used, because it is not of the right length, or contains indeces which do not belong to an existing wire. Please try again.")
                          pairpair <- applyURepeatX i n 3
                          case decEq ((snd pairpair).fst) i of
                            Yes prf1 => do
                              un <- runState
                              pure $ (Unitary.apply {i = i} {n = n} ui un (rewrite (sym prf1) in Builtin.DPair.DPair.snd (snd (pairpair))) {prf = ?whatnow2})
                            No prf2 => do
                              un <- get
                              pure un
                                        
{-                                       
apply : {i : Nat} -> {n : Nat} -> 
    (1 _ : Unitary i) -> (1 _ : Unitary n) -> 
    (v : Vect i Nat) -> 
    {auto prf : (IsInjectiveT n v)} -> 
    Unitary n

export
buildH : UStateT (Unitary 1) (Unitary 1) (Unitary 1) 
buildH = do 
  UStateT.pure HGate

export 
buildP : Double -> UStateT (Unitary 1) (Unitary 1) (Unitary 1) 
buildP p = do 
  UStateT.pure (PGate p)

export
buildID : UStateT (Unitary n) (Unitary n) (Unitary n)
buildID = do 
  UStateT.pure IdGate

export
tensorU : {n : Nat} -> {p : Nat} -> Unitary p -> UStateT (Unitary n) (Unitary n) (Unitary (n+p))
tensorU up = MkUST $ (\un => runUStateT un (UStateT.pure (tensor un up)))

export
tensorUF : {n : Nat} -> {p : Nat} -> Unitary p -> UStateT (Unitary n) (Unitary n) (Unitary (n+p))
tensorUF up = MkUST $ (\un => runUStateT un (UStateT.pure (tensor un up)))

private
tensorSepU : {n : Nat} -> {p : Nat} -> (1 _ : Unitary n) -> Unitary p -> UStateT (Unitary n) (Unitary n) (Unitary (n+p))
tensorSepU un up = (UStateT.pure (tensor un up))

export 
composeU : {n : Nat} -> Unitary n -> UStateT (Unitary n) (Unitary n) (Unitary n)
composeU fst = MkUST $ (\un => runUStateT un (UStateT.pure (compose fst un)))

myFunc : UStateT (Unitary 1) (Unitary 1) (Unitary 2)
myFunc = do 
  h <- buildH
  t <- tensorSepU h (PGate 1)
  UStateT.pure t --?what
  
-}
{-}
  ||| Apply a Unitary to another smaller one
  applyU : {n : Nat} -> {i : Nat} -> Unitary i -> {auto prf: LT i n} -> {auto valid: LTE 2 n} 
              -> UStateTT (LPair (Unitary n) (DPair (v: Vect n Nat) (IsInjective n v))) (LPair (Unitary n) (DPair (v: Vect n Nat) (IsInjective n v))) (Unitary n)
  applyU un = do
    [q1] <- apply {n = n} {i = rewrite (sym $ comeOnIdrisGen {n=n} {m=i} {prf = lteSuccLeft prf}) in (justFinLemma i (minus n i) {prf = rewrite lteSuccLeft in valid})}
              ui un wires  {valid = valid}
    pure q1 
  

                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
            run : UStateTT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool) -}