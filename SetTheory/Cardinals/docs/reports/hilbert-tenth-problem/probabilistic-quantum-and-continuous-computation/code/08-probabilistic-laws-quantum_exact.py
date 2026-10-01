"""Exact small quantum circuits in Z[sqrt(2), i]/2^L.

This is an exponential-size state-vector reference implementation, not an
asymptotically efficient classical simulation.  Each gate increments L by one.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Ring4:
    a: int = 0
    b: int = 0
    c: int = 0
    d: int = 0
    def __add__(self, o: "Ring4") -> "Ring4":
        return Ring4(self.a+o.a,self.b+o.b,self.c+o.c,self.d+o.d)
    def __neg__(self) -> "Ring4":
        return self.scale(-1)
    def __sub__(self, o: "Ring4") -> "Ring4":
        return self + (-o)
    def scale(self, k: int) -> "Ring4":
        return Ring4(k*self.a,k*self.b,k*self.c,k*self.d)
    def sqrt2(self) -> "Ring4":
        return Ring4(2*self.b,self.a,2*self.d,self.c)
    def times_i(self) -> "Ring4":
        return Ring4(-self.c,-self.d,self.a,self.b)
    def times_t_numerator(self) -> "Ring4":
        return (self+self.times_i()).sqrt2()
    def norm_coeffs(self) -> tuple[int,int]:
        return (self.a*self.a+2*self.b*self.b+self.c*self.c+2*self.d*self.d,
                2*(self.a*self.b+self.c*self.d))
    def approximate(self) -> complex:
        import math
        return complex(self.a+self.b*math.sqrt(2), self.c+self.d*math.sqrt(2))


def sign_sqrt2(a: int, b: int) -> int:
    """Sign of a+b*sqrt(2), without floating-point arithmetic."""
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0:
        return (b > 0) - (b < 0)
    if a > 0 and b > 0:
        return 1
    if a < 0 and b < 0:
        return -1
    cmp = (a*a > 2*b*b) - (a*a < 2*b*b)
    # Equality cannot occur for nonzero integers a,b (sqrt(2) is irrational).
    if cmp == 0:
        raise ArithmeticError("Unexpected nonzero integer solution a^2=2b^2")
    return cmp if a > 0 else -cmp


class Circuit:
    def __init__(self, qubits: int, basis: int = 0):
        if type(qubits) is not int or not 1 <= qubits <= 16:
            raise ValueError("Reference implementation supports 1..16 qubits")
        if type(basis) is not int or not 0 <= basis < (1 << qubits):
            raise ValueError("Invalid basis input")
        self.qubits = qubits
        self.L = 0
        self.state = [Ring4() for _ in range(1 << qubits)]
        self.state[basis] = Ring4(1)
    def apply(self, gate: str, target: int, control: int | None = None):
        if target not in range(self.qubits):
            raise ValueError("Invalid target")
        if gate not in {"H", "T", "X", "S", "CNOT"}:
            raise ValueError("Unknown gate")
        if gate == "CNOT" and (control not in range(self.qubits) or control == target):
            raise ValueError("CNOT requires a distinct valid control")
        old = self.state
        new = [Ring4() for _ in old]
        bit = 1 << target
        if gate == "H":
            for j in range(len(old)):
                if not (j & bit):
                    new[j] = (old[j]+old[j|bit]).sqrt2()
                    new[j|bit] = (old[j]-old[j|bit]).sqrt2()
        elif gate in {"T", "S"}:
            for j, z in enumerate(old):
                if not (j & bit):
                    new[j] = z.scale(2)
                elif gate == "T":
                    new[j] = z.times_t_numerator()
                else:
                    new[j] = z.times_i().scale(2)
        else:
            for j, z in enumerate(old):
                do_flip = gate == "X" or bool(j & (1 << control))
                new[j ^ bit if do_flip else j] = z.scale(2)
        self.state = new
        self.L += 1
        return self
    def probability(self, indices) -> tuple[Fraction, Fraction]:
        inds = list(indices)
        if len(set(inds)) != len(inds) or any(i not in range(len(self.state)) for i in inds):
            raise ValueError("Indices must be distinct valid basis states")
        A=B=0
        for i in inds:
            a,b = self.state[i].norm_coeffs()
            A+=a; B+=b
        return Fraction(A,4**self.L),Fraction(B,4**self.L)
    def assert_normalized(self):
        assert self.probability(range(len(self.state))) == (Fraction(1),Fraction(0))
