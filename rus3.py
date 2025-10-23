import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.reset(0)
	return circuit


def Function1(circuit):  
	circuit.reset(1)
	return circuit


def Function2(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllUnitariesBeforeFunc3InOne(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllFunctionsBefore3(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	return circuit


def Function3(circuit): 
	circuit.measure(1, 1)
	return circuit


def Function4(circuit):  
	circuit.p(-np.pi/4, 0)
	return circuit


def Function5(circuit):  
	circuit.reset(1)
	return circuit


def Function6(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllUnitariesBeforeFunc7InOne(circuit):  
	circuit.p(-np.pi/4, 0)
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllFunctionsBefore7(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	Function6(circuit)
	return circuit


def Function7(circuit): 
	circuit.measure(1, 1)
	return circuit


def AllUnitariesBeforeFunc8InOne(circuit):  
	return circuit


def AllFunctionsBefore8(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	Function6(circuit)
	Function7(circuit)
	return circuit


def Function8(circuit): 
	circuit.measure(0, 0)
	return circuit

def OutputCircuit(n):  
	circuit = QuantumCircuit(n, n)
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	Function6(circuit)
	Function7(circuit)
	Function8(circuit)
	return circuit

qc = OutputCircuit(2)

print(qc)
