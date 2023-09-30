module UState
import Control.Monad.State
import LinearTypes
import Control.Linear.LIO
import Unitary

public export
R : Type -> Type
R = L IO {use = Linear}

public export
data UState : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkUS : ((initialType) -> IO (Pair finalType returnType)) -> UState initialType finalType returnType


||| Unwrap and apply a UState monad computation.
public export
runUState : initialType ->  UState initialType finalType returnType -> IO (Pair finalType returnType)
runUState i (MkUS f) = f i


public export
pure : ( a) -> UState t t a
pure x = MkUS (\st => pure (MkPair st x))

public export
pureF : (a) -> (f: b->t) -> UState b t a 
pureF x f = MkUS (\st => pure (MkPair (f st) x))


public export
(>>=) : (UState i m a) -> ((a -> UState m o b)) -> UState i o b
v >>= f = MkUS $ \i => do 
                         (MkPair  a m) <- runUState i v
                         runUState a (f m)


public export
modify : (i-> o) -> UState i o ()
modify f = MkUS $ \i => pure (MkPair (f i) ())

Functor (\a => (IO (Pair a a))) where
  map f any = do 
    (MkPair c d) <- any
    pure (MkPair (f c) (f d))

Functor f => Applicative (\a => (IO (Pair a a))) where
  pure = (\fst => pure (MkPair fst fst))
  (<*>) fg st = do 
      MkPair f g <- fg
      MkPair c d <- st
      pure (MkPair (f c) (g d))


implementation Functor (UState (Unitary n) (Unitary n)) where
  map func fa = do
    a <- fa
    pure (func a)

implementation Functor f => Applicative (UState (Unitary n) (Unitary n)) where
  pure a =  UState.pure a
  (<*>) fg st = do 
      func <- fg
      un <- st
      pure $ func un

  {-}
Functor (\a => (R (Pair a a))) where
  map f any = do 
    (MkPair c d) <- any
    pure1 (MkPair (f c) (f d))

Functor (\a => (R (Pair a b))) where
    map f any = do 
      (MkPair c d) <- any
      pure1 (MkPair (f c) d)

Functor (\b => (R (Pair a b))) where
  map f any = do 
    (MkPair c d) <- any
    pure1 (MkPair c (f d))

Functor f => Applicative (\a => (R (Pair a a))) where
    pure = (\fst => pure1 (MkPair fst fst))
    (<*>) fg st = do 
       MkPair f g<- fg
       MkPair c d <- st
       pure1 (MkPair (f c) (g d))

Functor f => Applicative (\a => (R (Pair a () ))) where
    pure = (\fst => pure1 (MkPair fst () ))
    (<*>) fg st = do 
      MkPair f g<- fg
      MkPair c d <- st
      pure1 (MkPair (f c) d)

Functor f => Applicative (\b => (R (Pair () b))) where
    pure = (\snd => pure1 (MkPair () snd))
    (<*>) fg st = do 
      MkPair f g <- fg
      MkPair c d <- st
      pure1 (MkPair c (g d))


    {
export
getU : UState s m s
getU = MkUS $ \s => do
pure (MkPair s s)-}