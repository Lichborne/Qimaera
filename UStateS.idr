module UStateS
import Control.Monad.State
import LinearTypes
import Control.Linear.LIO

public export
R : Type -> Type
R = L IO {use = Linear}



public export
data UStateS : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkUSS : (1 _ : (1 _ : initialType) -> R (Pair finalType returnType)) -> UStateS initialType finalType returnType


||| Unwrap and apply a UStateS monad computation.
public export
runUStateS : (1 _ : initialType) -> (1 _ : UStateS initialType finalType returnType) -> R (Pair finalType returnType)
runUStateS i (MkUSS f) = f i


public export
pure : (1 _ : a) -> UStateS t t a
pure x = MkUSS (\st => pure1 (MkPair st x))


public export
(>>=) : (1 _ : UStateS i m a) -> (1 _ : ((1 _ : a) -> UStateS m o b)) -> UStateS i o b
v >>= f = MkUSS $ \i => do 
                         (MkPair a m) <- runUStateS i v
                         runUStateS a (f m)


public export
modify : ((1 _ : i) -> o) -> UStateS i o ()
modify f = MkUSS $ \i => pure1 (f i # ())

{-
get : UStateS s m s
get = MkUSS $ (\s => do
      pure s)}
   ||| Apply the Hadamard gate 
  applyH : {n : Nat} -> Unitary i -> Unitary n -> {auto prf: LT i n} -> {auto valid: LTE 2 n} 
              -> UStateS (Vect i (Fin n)) (Vect n (Fin )) (Unitary n)
  applyH ui un q = do
    wires <- get
    [q1] <- apply {n = n} {i = rewrite (sym $ comeOnIdrisGen {n=n} {m=i} {prf = lteSuccLeft prf}) in (justFinLemma i (minus n i) {prf = rewrite lteSuccLeft in valid})}
              ui un wires  {valid = valid}
    pure q1 

-}