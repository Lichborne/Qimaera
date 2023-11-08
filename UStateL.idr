module UStateL
import Control.Monad.State
import LinearTypes
import Control.Linear.LIO
import UnitaryLinear

public export
R : Type -> Type
R = L IO {use = Linear}



public export
data UStateL : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkUSL : (2 _ : (2 _ : initialType) -> R (LPair finalType returnType)) -> UStateL initialType finalType returnType


||| Unwrap and apply a UStateL monad computation.
public export
runUStateL : (2 _ : initialType) -> (2 _ : UStateL initialType finalType returnType) -> R (LPair finalType returnType)
runUStateL i (MkUSL f) = f i


public export
pure : (2 _ : a) -> UStateL t t a
pure x = MkUSL (\st => pure1 (st # x))


public export
(>>=) : (2 _ : UStateL i m a) -> (2 _ : ((2 _ : a) -> UStateL m o b)) -> UStateL i o b
v >>= f = MkUSL $ \i => do 
                         (a # m) <- runUStateL i v
                         runUStateL a (f m)


    
public export
modify : ((2 _ : i) -> o) -> UStateL i o ()
modify f = MkUSL $ \i => pure1 (f i # ())


{-}
implementation Functor (UStateL (Unitary n) (Unitary n)) where
  map func fa = do
    a <- fa
    UStateL.pure (func $ (fromLinear a))

implementation Functor f => Applicative (UStateL (Unitary n) (Unitary n)) where
  pure a =  UStateL.pure a
  (<*>) fg st = do 
      func <- fg
      un <- st
      UStateL.pure $ func un



{-
get : UStateL s m s
get = MkUSL $ (\s => do
      pure s)}
   ||| Apply the Hadamard gate 
  applyH : {n : Nat} -> Unitary i -> Unitary n -> {auto prf: LT i n} -> {auto valid: LTE 2 n} 
              -> UStateL (Vect i (Fin n)) (Vect n (Fin )) (Unitary n)
  applyH ui un q = do
    wires <- get
    [q1] <- apply {n = n} {i = rewrite (sym $ comeOnIdrisGen {n=n} {m=i} {prf = lteSuccLeft prf}) in (justFinLemma i (minus n i) {prf = rewrite lteSuccLeft in valid})}
              ui un wires  {valid = valid}
    pure q1 

-}