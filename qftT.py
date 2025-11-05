import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.reset(0)
	circuit.reset(1)
	circuit.reset(2)
	return circuit


def Function1(circuit):  
	circuit.h(2)
	circuit.p(np.pi/4, 2)
	circuit.cx(1, 2)
	circuit.p(-np.pi/4, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/8, 2)
	circuit.cx(0, 2)
	circuit.p(-np.pi/8, 2)
	circuit.cx(0, 2)
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(0, 1)
	circuit.p(-np.pi/4, 1)
	circuit.cx(0, 1)
	circuit.h(0)
	return circuit


def AllUnitariesBeforeFunc2InOne(circuit):  
	circuit.h(2)
	circuit.p(np.pi/4, 2)
	circuit.cx(1, 2)
	circuit.p(-np.pi/4, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/8, 2)
	circuit.cx(0, 2)
	circuit.p(-np.pi/8, 2)
	circuit.cx(0, 2)
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(0, 1)
	circuit.p(-np.pi/4, 1)
	circuit.cx(0, 1)
	circuit.h(0)
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

print(qc)