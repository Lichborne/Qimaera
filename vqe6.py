import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-2.445196200109178, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-4.437747944106293, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(2.0573473888831755, 1)
	circuit.p(2.442409619643624, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-1.8454860919824496, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-0.9077803260105465, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.11405874266303555, 1)
	circuit.p(1.8298981081710137, 2)
	return circuit


def Function1(circuit):  
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.h(2)
	circuit.cx(2, 0)
	return circuit


def AllUnitariesBeforeFunc2InOne(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-2.445196200109178, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-4.437747944106293, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(2.0573473888831755, 1)
	circuit.p(2.442409619643624, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-1.8454860919824496, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-0.9077803260105465, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.11405874266303555, 1)
	circuit.p(1.8298981081710137, 2)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.h(2)
	circuit.cx(2, 0)
	return circuit


def AllFunctionsBefore2(circuit): 
	Function0(circuit)
	Function1(circuit)
	return circuit


def Function2(circuit): 
	circuit.measure_all()
	return circuit

def OutputCircuit(n):  
	circuit = QuantumCircuit(n, n)
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	return circuit

qc = OutputCircuit(3)