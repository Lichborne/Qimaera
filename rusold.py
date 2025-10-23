import numpy as np
from qiskit import QuantumCircuit
from qiskit import QuantumRegister
qr = QuantumRegister(1)
qc = QuantumCircuit(qr)

qc.h(qr[1])
qc.barrier(qr)
qc.p(np.pi/4, qr[1])
qc.barrier(qr)
qc.cx(qr[1], qr[0])
qc.barrier(qr)
qc.h(qr[1])
qc.barrier(qr)
qc.cx(qr[1], qr[0])
qc.barrier(qr)
qc.p(np.pi/4, qr[1])
qc.barrier(qr)
qc.h(qr[1])
qc.barrier(qr)

print(qc)