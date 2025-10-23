import numpy as np
from qiskit import QuantumCircuit
from qiskit import QuantumRegister
qr = QuantumRegister(5)
qc = QuantumCircuit(qr)

qc.cx(qr[2], qr[0])
qc.barrier(qr)
qc.h(qr[3])
qc.barrier(qr)
qc.cx(qr[3], qr[0])
qc.barrier(qr)
qc.h(qr[4])
qc.barrier(qr)
qc.cx(qr[4], qr[0])
qc.barrier(qr)

print(qc)