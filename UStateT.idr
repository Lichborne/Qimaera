module UStateT
import Control.Monad.State
import LinearTypes
import Control.Linear.LIO

public export
R : Type -> Type
R = L IO {use = Linear}



public export
data UStateT : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkUST : (1 _ : (1 _ : initialType) -> R (LPair finalType returnType)) -> UStateT initialType finalType returnType


||| Unwrap and apply a UStateT monad computation.
public export
runUStateT : (1 _ : initialType) -> (1 _ : UStateT initialType finalType returnType) -> R (LPair finalType returnType)
runUStateT i (MkUST f) = f i


public export
pure : (1 _ : a) -> UStateT t t a
pure x = MkUST (\st => pure1 (st # x))


public export
(>>=) : (1 _ : UStateT i m a) -> (1 _ : ((1 _ : a) -> UStateT m o b)) -> UStateT i o b
v >>= f = MkUST $ \i => do 
                         (a # m) <- runUStateT i v
                         runUStateT a (f m)


public export
modify : ((1 _ : i) -> o) -> UStateT i o ()
modify f = MkUST $ \i => pure1 (f i # ())


{-

   ||| Apply the Hadamard gate 
  applyH : {n : Nat} -> Unitary i -> Unitary n -> {auto prf: LT i n} -> {auto valid: LTE 2 n} 
              -> UStateT (Vect i (Fin n)) (Vect n (Fin )) (Unitary n)
  applyH ui un q = do
    wires <- get
    [q1] <- apply {n = n} {i = rewrite (sym $ comeOnIdrisGen {n=n} {m=i} {prf = lteSuccLeft prf}) in (justFinLemma i (minus n i) {prf = rewrite lteSuccLeft in valid})}
              ui un wires  {valid = valid}
    pure q1 

-}