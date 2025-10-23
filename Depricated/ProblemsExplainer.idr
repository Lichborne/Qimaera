x3 : Unitary 3 
x3 = (X 0 (IdGate))

-- In this example, wew try to reuse a qubit that has be measured
ux :  UnitaryOp t => {n:Nat} -> (1 _ : LVect 3 Qubit) -> UStateT (t (n)) (t (n)) (LVect 3 Qubit)
ux qs = do 
            [q1,q2,q3] <- applyUnitary qs (x3)
            pure [q1,q2,q3]

Error: While processing right hand side of ux. When unifying:
    Unitary 3
and:
    Unitary 3
Mismatch between: Unitary 3 and Unitary 3.

ExampleDetectableErrors:65:44--65:46
 61 | 
 62 | -- In this example, wew try to reuse a qubit that has be measured
 63 | ux :  UnitaryOp t => {n:Nat} -> (1 _ : LVect 3 Qubit) -> UStateT (t (n)) (t (n)) (LVect 3 Qubit)
 64 | ux qs = do 
 65 |             [q1,q2,q3] <- applyUnitary qs (x3)