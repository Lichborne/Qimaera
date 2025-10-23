import numpy as np
from qiskit import QuantumCircuit
def OutputCircuit():  
	circuit = QuantumCircuit(3, 3)

def Function0(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-3.87166556081694, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-4.54372298692971, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(6.072446334993537, 1)
	circuit.p(5.887670479891309, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-2.4639325392469016, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.239369101714623, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(3.9805810211222723, 1)
	circuit.p(5.72582967798267, 2)
	return circuit
def Function1(circuit):  
	circuit.cx(2, 0)
	return circuit
def AllUnitariesBefore2InOne(circuit):  
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-3.87166556081694, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-4.54372298692971, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(6.072446334993537, 1)
	circuit.p(5.887670479891309, 2)
	circuit.cx(1, 2)
	circuit.p(np.pi/2, 1)
	circuit.h(1)
	circuit.p(-2.4639325392469016, 1)
	circuit.h(1)
	circuit.p(-np.pi/2, 1)
	circuit.p(np.pi/2, 2)
	circuit.h(2)
	circuit.p(-2.239369101714623, 2)
	circuit.h(2)
	circuit.p(-np.pi/2, 2)
	circuit.p(3.9805810211222723, 1)
	circuit.p(5.72582967798267, 2)
	circuit.cx(2, 0)

	return circuit


def AllFunctionsBefore2(circuit): 
	Function0(circuit)
	Function1(circuit)
circui.measure_all()	return circuit 

qc = OutputCircuit()