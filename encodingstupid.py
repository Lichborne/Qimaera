import numpy as np
from qiskit import QuantumCircuit
from qiskit import QuantumRegister
qr = QuantumRegister(3)
qc = QuantumCircuit(qr)

qc.cx(qr[2], qr[0])
qc.barrier(qr)

print(qc)