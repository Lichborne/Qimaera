import numpy as np
from qiskit import QuantumCircuit


def Function0(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-4.4970594446357905, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-0.8001959606578453, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(6.19935821380829, 1)
	circuit.p(6.066543249129476, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-4.9784424423832725, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.090741273767426, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.22315658001931715, 1)
	circuit.p(6.139953661524965, 2)
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
	circuit.p(-4.4970594446357905, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-0.8001959606578453, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(6.19935821380829, 1)
	circuit.p(6.066543249129476, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-4.9784424423832725, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.090741273767426, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(0.22315658001931715, 1)
	circuit.p(6.139953661524965, 2)
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