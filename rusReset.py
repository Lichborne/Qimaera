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
	circuit.reset(1)
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
	circuit.reset(1)
	return circuit


def Function5(circuit):  
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
	circuit.reset(1)
	return circuit


def Function8(circuit):  
	return circuit


def Function9(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllUnitariesBeforeFunc10InOne(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllFunctionsBefore10(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	Function6(circuit)
	Function7(circuit)
	Function8(circuit)
	Function9(circuit)
	return circuit


def Function10(circuit): 
	circuit.measure(1, 1)
	circuit.reset(1)
	return circuit


def Function11(circuit):  
	return circuit


def Function12(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllUnitariesBeforeFunc13InOne(circuit):  
	circuit.h(1)
	circuit.p(np.pi/4, 1)
	circuit.cx(1, 0)
	circuit.h(1)
	circuit.cx(1, 0)
	circuit.p(np.pi/4, 1)
	circuit.h(1)
	return circuit


def AllFunctionsBefore13(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	Function6(circuit)
	Function7(circuit)
	Function8(circuit)
	Function9(circuit)
	Function10(circuit)
	Function11(circuit)
	Function12(circuit)
	return circuit


def Function13(circuit): 
	circuit.measure(1, 1)
	circuit.reset(1)
	return circuit


def AllUnitariesBeforeFunc14InOne(circuit):  
	return circuit


def AllFunctionsBefore14(circuit): 
	Function0(circuit)
	Function1(circuit)
	Function2(circuit)
	Function3(circuit)
	Function4(circuit)
	Function5(circuit)
	Function6(circuit)
	Function7(circuit)
	Function8(circuit)
	Function9(circuit)
	Function10(circuit)
	Function11(circuit)
	Function12(circuit)
	Function13(circuit)
	return circuit


def Function14(circuit): 
	circuit.measure(0, 0)
	circuit.reset(0)
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
	Function9(circuit)
	Function10(circuit)
	Function11(circuit)
	Function12(circuit)
	Function13(circuit)
	Function14(circuit)
	return circuit

qc = OutputCircuit(2)

print(qc)