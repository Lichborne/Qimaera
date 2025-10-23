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
 ++ 	reset(1)
	return circuit


def Function2(circuit):  
	return circuit


def Function3(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllUnitariesBeforeFunc4InOne(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllFunctionsBefore4(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	return circuit


def Function4(circuit): 
	circuit.measure(1, 1)
 ++ 	reset(1)
	return circuit


def AllUnitariesBeforeFunc5InOne(circuit):  
	return circuit


def AllFunctionsBefore5(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	return circuit


def Function5(circuit): 
	circuit.measure(0, 0)
 ++ 	reset(0)
	return circuit

def OutputCircuit(n):  
	circuit = QuantumCircuit(n, n)
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	return circuit

qc = OutputCircuit(1)