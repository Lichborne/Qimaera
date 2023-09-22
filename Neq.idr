module Neq

import Data.Nat

public export

data NEQ : (left,right:Nat) -> Type where
    ZEQL : NEQ Z (S right)
    ZEQR : NEQ (S left) Z
    SEQL : NEQ Z right -> NEQ (S Z) (S right)
    SEQR : NEQ left Z -> NEQ (S left) (S Z)
    SEQ  : NEQ (S left) (S right) -> NEQ (S (S left)) (S (S right))