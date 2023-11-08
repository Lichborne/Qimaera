module ManyValued 
import Data.Stream
import Data.List
import Data.Vect
import Prelude.Uninhabited

%default partial

data Triple : a -> b -> c -> Type where
    MkTriple : a -> b -> c -> Triple a b c



isNonEmpty : (l:List a) -> Dec (NonEmpty l)
isNonEmpty Nil = No (uninhabited)
isNonEmpty (x::xs) = Yes (IsNonEmpty)

P = (Stream Bool)

partial
Eq RZ1 where
    (==) ((::) True rest1) ((::) False rest2) = False
    (==) ((::) False rest1) ((::) True rest2) = False
    (==) ((::) True rest1) ((::) True rest2) = rest1 == rest2
    (==) ((::) False rest1) ((::) False rest2) = rest1 == rest2

partial
Eq RZ1 => Ord RZ1 where
    compare ((::) True rest1) ((::) False rest2) = GT
    compare ((::) False rest1) ((::) True rest2) = LT
    compare ((::) True rest1) ((::) True rest2) = compare rest1 rest2
    compare ((::) False rest1) ((::) False rest2) = compare rest1 rest2

partial
plusAuxP : RZ1 -> RZ1 -> Pair Bool RZ1
plusAuxP (False::xs) (False::ys) = case (plusAuxP xs ys) of 
                                        (True, xss) => MkPair False (True::xss) 
                                        (False, yss) => MkPair False (False::yss)
plusAuxP (False::xs) (True::ys) = case (plusAuxP xs ys) of 
                                    (True, xss) => MkPair True (False::xss) 
                                    (False, yss) => MkPair False (True::yss)
plusAuxP (True::xs) (False::ys) = case (plusAuxP xs ys) of 
                                    (True, xss) => MkPair True (False::xss) 
                                    (False, yss) => MkPair False (True::yss)
plusAuxP (True::xs) (True::ys) = case (plusAuxP xs ys) of 
                                    (True, xss) => MkPair True (True::xss) 
                                    (False, yss) => MkPair True (False::yss)

partial
plusP : RZ1 -> RZ1 -> RZ1
plusP (True::rest1) (True::rest2) = repeat True --if greater than one, then one
plusP (True::True::rest1) (False::True::rest2) = repeat True --if greater than one, then one
plusP (False::True::rest1) (True::True::rest2) = repeat True --if greater than one, then one
plusP (False::rest1) (False::rest2) = case plusAuxP rest1 rest2 of 
                                        (True, any1) => True::any1
                                        (False, any2) => False::any2 


FinP = Vect 1000 Bool

Eq FinP where
    (==) ((::) True rest1) ((::) False rest2) = False
    (==) ((::) False rest1) ((::) True rest2) = False
    (==) ((::) True rest1) ((::) True rest2) = rest1 == rest2
    (==) ((::) False rest1) ((::) False rest2) = rest1 == rest2

Eq FinP => Ord FinP where
    compare ((::) True rest1) ((::) False rest2) = GT
    compare ((::) False rest1) ((::) True rest2) = LT
    compare ((::) True rest1) ((::) True rest2) = compare rest1 rest2
    compare ((::) False rest1) ((::) False rest2) = compare rest1 rest2


plusAuxFinP  : Vect n Bool -> Vect n Bool -> Pair Bool (Vect n Bool)
plusAuxFinP  [] _ = MkPair False []
plusAuxFinP  _ [] = MkPair False []
plusAuxFinP  (False::xs) (False::ys) = case (plusAuxFinP  xs ys) of 
                                        (True, xss) => MkPair False (True::xss) 
                                        (False, yss) => MkPair False (False::yss)
plusAuxFinP  (False::xs) (True::ys) = case (plusAuxFinP  xs ys) of 
                                    (True, xss) => MkPair True (False::xss) 
                                    (False, yss) => MkPair False (True::yss)
plusAuxFinP  (True::xs) (False::ys) = case (plusAuxFinP  xs ys) of 
                                    (True, xss) => MkPair True (False::xss) 
                                    (False, yss) => MkPair False (True::yss)
plusAuxFinP  (True::xs) (True::ys) = case (plusAuxFinP  xs ys) of 
                                    (True, xss) => MkPair True (True::xss) 
                                    (False, yss) => MkPair True (False::yss)

plusFinP : {n:Nat} -> Vect n Bool -> Vect n Bool -> Vect n Bool
plusFinP (True::rest1) (True::rest2) = replicate n True --if greater than one, then one
plusFinP (True::True::rest1) (False::True::rest2) = replicate n True --if greater than one, then one
plusFinP (False::True::rest1) (True::True::rest2) = replicate n True --if greater than one, then one
plusFinP (False::rest1) (False::rest2) = case plusAuxFinP rest1 rest2 of 
                                        (True, any1) => True::any1
                                        (False, any2) => False::any2
(+) : {n:Nat} -> Vect n Bool -> Vect n Bool -> Vect n Bool
(+) = plusFinP

minusAuxFinP  : Vect n Bool -> Vect n Bool -> Pair Bool (Vect n Bool)
minusAuxFinP  [] _ = MkPair False []
minusAuxFinP  _ [] = MkPair False []
minusAuxFinP  (False::xs) (False::ys) = case (minusAuxFinP  xs ys) of 
                                        (True, xss) => MkPair True (True::xss) 
                                        (False, yss) => MkPair False (False::yss)
minusAuxFinP  (False::xs) (True::ys) = case (minusAuxFinP  xs ys) of 
                                    (True, xss) => MkPair True (False::xss) 
                                    (False, yss) => MkPair True (True::yss)
minusAuxFinP  (True::xs) (False::ys) = case (minusAuxFinP  xs ys) of 
                                    (True, xss) => MkPair False (False::xss) 
                                    (False, yss) => MkPair False (True::yss)
minusAuxFinP  (True::xs) (True::ys) = case (minusAuxFinP  xs ys) of 
                                    (True, xss) => MkPair True (True::xss) 
                                    (False, yss) => MkPair False (False::yss)

minusFinPZTest : Vect n Bool -> Vect n Bool -> Bool
minusFinPZTest [] [] = False
minusFinPZTest (False::xs) (True::ys) = True
minusFinPZTest (True::xs) (False::ys) = False
minusFinPZTest (True::xs) (True::ys) = minusFinPZTest xs ys 
minusFinPZTest (False::xs) (False::ys) = minusFinPZTest xs ys 

minusFinP : {n:Nat} -> Vect n Bool -> Vect n Bool -> Vect n Bool
minusFinP (False::xs) (True::ys) = replicate n False
minusFinP (True::xs) (False::ys) = case minusAuxFinP xs ys of
                                    (True, ts) => False::ts
                                    (False, fs) => True::fs
minusFinP {n = S k} (True::xs) (True::ys) = case minusAuxFinP xs ys of
                                    (True, ts) => replicate (S k) False -- once again, if second number is bigger, then zero
                                    (False, fs) => False::fs
minusFinP {n = S k} (False::xs) (False::ys) = case minusAuxFinP xs ys of
                                        (True, ts) => replicate (S k) False -- once again, if second number is bigger, then zero
                                        (False, fs) => False::fs

(-) : {n:Nat} -> Vect n Bool -> Vect n Bool -> Vect n Bool
(-) = minusFinP

multFinPAux : {n:Nat} -> {k:Nat} -> Vect n Bool -> Vect k Bool -> Vect n Bool
multFinPAux [] [] = []
multFinPAux a [] = replicate n False
multFinPAux [] b = []
multFinPAux (a) (True::bs) = a
multFinPAux (a::as) (False::bs) = replicate n False

expandLeft : {n:Nat} -> Vect n Bool -> Vect n Bool -> Vect (S n) Bool
expandLeft a [] = (replicate (S n) False)
expandLeft a (b) = ((Data.Vect.(::) False (multFinPAux a (b))))

expandRight : {n:Nat} -> Vect n Bool -> Vect n Bool -> Vect (S n) Bool
expandRight a [] = (replicate (S n) False)
expandRight a (b) = (rewrite plusOneSucc n in (rewrite sym $ plusCommutative n 1 in (Data.Vect.(++) (multFinPAux a (b)) [False])))

multFinPFull : {n:Nat} -> {k:Nat} -> Vect n Bool -> Vect n Bool -> Vect n Bool
multFinPFull [] [] = []
multFinPFull a (b::bs) = multFinPFull (expandLeft a (b::bs) + expandRight a bs)

multFinP : FinP -> FinP -> FinP
multFinP a b = take 1000 (multFinPAux a b)

{- plusFinP (False::False::True::False::False::True::(replicate 994 False)) (False::True::True::True::False::False::(replicate 994 False)) 
minusFinP (False::False::True::False::False::True::(replicate 994 False)) (False::True::True::True::False::False::(replicate 994 False)) 

minusFinP (False::True::True::True::False::False::(replicate 994 False)) (False::False::True::False::False::True::(replicate 994 False)) 

1. write QFT using Quantum Op without unitary
2. design UStateT similar
3. write QFT using UStateT
4. write a linear function from linear vector of size n to size n with arbitrary a 
                                        -}

data P : x -> s -> Type

