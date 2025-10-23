import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-4.407593331018798, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-1.5490886459708098, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(2.94987984408562, 1)
	circuit.p(5.76171023649396, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-2.35510733401515, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.1981910147367585, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(1.16107388618492, 1)
	circuit.p(1.9044001285470231, 2)
	return circuit


def Function1(circuit):  
	circuit.cx(2, 0)
	return circuit


def AllUnitariesBeforeFunc2InOne(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-4.407593331018798, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-1.5490886459708098, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(2.94987984408562, 1)
	circuit.p(5.76171023649396, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-2.35510733401515, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.1981910147367585, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(1.16107388618492, 1)
	circuit.p(1.9044001285470231, 2)
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

