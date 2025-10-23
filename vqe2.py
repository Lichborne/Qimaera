import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-3.695718299769349, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-5.810946587028475, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.7124307910487094, 1)
	circuit.p(5.42063781345147, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-1.546494876507085, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.1325029349667006, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.7639473803124813, 1)
	circuit.p(4.584877343684393, 2)
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
	circuit.p(-3.695718299769349, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-5.810946587028475, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.7124307910487094, 1)
	circuit.p(5.42063781345147, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-1.546494876507085, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.1325029349667006, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.7639473803124813, 1)
	circuit.p(4.584877343684393, 2)
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