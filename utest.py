import numpy as np
from qiskit import QuantumCircuit
from qiskit import QuantumRegister
qr = QuantumRegister(4)
qc = QuantumCircuit(qr)

qc.p(0.1, qr[1])
qc.barrier(qr)
qc.h(qr[0])
qc.barrier(qr)
qc.cx(qr[1], qr[3])
qc.barrier(qr)

print(qc)