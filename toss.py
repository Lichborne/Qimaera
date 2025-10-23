import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.reset(0)
	return circuit


def Function1(circuit):  
	circuit.h(0)
	return circuit


def AllUnitariesBeforeFunc2InOne(circuit):  
	circuit.h(0)
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