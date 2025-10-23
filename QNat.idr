module QNat

import Data.Nat
import Data.Vect
import Data.Vect.Sort
import Data.Vect.Elem
import Decidable.Equality
import Complex
import NatRules
import LinearTypes
import public Data.Linear.Notation
import public Data.Linear.Interface
import System
import Data.Linear
import Lemmas


data Stream : Type -> Type where
       (::) : a -> Inf (Stream a) -> Stream a
export
data QNat : Type where
  Stream Bool