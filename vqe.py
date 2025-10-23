import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllUnitariesBeforeFunc1InOne(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllFunctionsBefore1(circuit): 
	Function0(circuit)
	return circuit


def Function1(circuit): 
	circuit.measure(1, 1)
	return circuit


def AllUnitariesBeforeFunc2InOne(circuit):  
	return circuit


def AllFunctionsBefore2(circuit): 
	Function0(circuit)
	Function1(circuit)
	return circuit


def Function2(circuit): 
	circuit.measure(0, 0)
	return circuit

def OutputCircuit(n):  
	circuit = QuantumCircuit(n, n)
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	return circuit

qc = OutputCircuit(1)