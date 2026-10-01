"""Clock-independent, unique-witness quartic certificate compiler.

The polynomial is represented exactly as a sum of squares of sparse
quadratic residuals. All variables, including witnesses, range over N.
The JSON format is an exact polynomial representation, not a numeric fit.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Mapping
from padic_machine import Machine, natural


class Poly:
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = dict(value.terms)
        elif isinstance(value, str):
            self.terms = {(value,): 1}
        elif isinstance(value, int):
            self.terms = {(): value} if value else {}
        elif isinstance(value, dict):
            self.terms = {k: v for k,v in value.items() if v}
        else:
            raise TypeError("unsupported polynomial input")

    def __add__(self, other):
        out = dict(self.terms)
        for mon, coeff in Poly(other).terms.items():
            out[mon] = out.get(mon, 0) + coeff
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m,c in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly(other))

    def __rsub__(self, other):
        return Poly(other) + (-self)

    def __mul__(self, other):
        out = {}
        for m,c in self.terms.items():
            for n,d in Poly(other).terms.items():
                mon = tuple(sorted(m+n))
                out[mon] = out.get(mon, 0) + c*d
        return Poly(out)

    __rmul__ = __mul__

    @property
    def degree(self):
        return max((len(m) for m in self.terms), default=0)

    def evaluate(self, values: Mapping[str, int]) -> int:
        result = 0
        for mon, coeff in self.terms.items():
            term = coeff
            for name in mon:
                term *= values[name]
            result += term
        return result

    def json(self):
        return [{"coefficient": c, "factors": list(m)}
                for m,c in sorted(self.terms.items())]


@dataclass
class Certificate:
    machine: Machine
    T: int
    S: int
    variables: list[str]
    residuals: list[tuple[str, Poly]]

    def evaluate(self, n: int, witness: Mapping[str, int]) -> int:
        natural(n, "n")
        if set(witness) != set(self.variables):
            raise ValueError("witness must have exactly the declared coordinates")
        values = {k: natural(v, k) for k,v in witness.items()}
        values["n"] = n
        return sum(p.evaluate(values)**2 for _,p in self.residuals)

    def json(self):
        return {"domain": "nonnegative integers", "parameter": "n",
                "polynomial": "sum of squares of residuals",
                "degree_upper_bound": 4,
                "time_bound": self.T, "input_bits": self.S,
                "machine": self.machine.description(),
                "variables": self.variables,
                "residuals": [{"label": label, "terms": p.json()}
                              for label,p in self.residuals]}


def compile_certificate(M: Machine, T: int, S: int) -> Certificate:
    natural(T, "T"); natural(S, "S")
    names: list[str] = []
    name_set: set[str] = set()
    equations: list[tuple[str, Poly]] = []

    def var(name: str):
        if name not in name_set:
            name_set.add(name)
            names.append(name)
        return Poly(name)

    def eq(label: str, p: Poly):
        assert p.degree <= 2
        equations.append((label, p))

    d = [var(f"d_{i}") for i in range(S)]
    x = [var(f"x_{i}") for i in range(S+1)]
    y = [var(f"y_{i}") for i in range(S+1)]
    L = [var(f"L_{t}") for t in range(T+1)]
    R = [var(f"R_{t}") for t in range(T+1)]
    state = [[var(f"s_{t}_{q}") for q in range(M.m)] for t in range(T+1)]
    for i in range(S):
        eq(f"input bit {i}", d[i]*(d[i]-1))
    eq("initial binary accumulator", x[0])
    eq("initial base-four accumulator", y[0])
    for i in range(S):
        eq(f"binary Horner {i}", x[i+1]-2*x[i]-d[S-1-i])
        eq(f"base-four Horner {i}", y[i+1]-4*y[i]-d[S-1-i])
    eq("input packing", Poly("n")-1-2*M.start-(1 << (M.r+2))*y[S])
    eq("initial left tape", L[0])
    eq("initial right tape", R[0]-x[S])
    for t in range(T+1):
        for q in range(M.m):
            eq(f"state bit {t}/{q}", state[t][q]*(state[t][q]-1))
        eq(f"one state {t}", sum(state[t], Poly())-1)
    for q in range(M.m):
        eq(f"initial state {q}", state[0][q]-int(q == M.start))
    for t in range(T):
        a,b,A,B = [var(f"{label}_{t}") for label in ("a","b","A","B")]
        eq(f"left division {t}", L[t]-2*A-a)
        eq(f"right division {t}", R[t]-2*B-b)
        eq(f"left bit {t}", a*(a-1))
        eq(f"right bit {t}", b*(b-1))
        nextstate = [Poly() for _ in range(M.m)]
        nextL, nextR = Poly(), Poly()
        for q in range(M.m):
            for read in (0,1):
                e = var(f"e_{t}_{q}_{read}")
                eq(f"selector {t}/{q}/{read}",
                   e-state[t][q]*(b if read else 1-b))
                if q == M.halt:
                    target, U, V = q, L[t], R[t]
                else:
                    rule = M.rules[(q,read)]
                    target, w = rule.target, rule.write
                    if rule.move == "R":
                        U,V = 2*L[t]+w,B
                    elif rule.move == "L":
                        U,V = A,a+2*w+4*B
                    else:
                        U,V = L[t],w+2*B
                nextstate[target] += e
                nextL += e*U; nextR += e*V
        for q in range(M.m):
            eq(f"state update {t}/{q}", state[t+1][q]-nextstate[q])
        eq(f"left update {t}", L[t+1]-nextL)
        eq(f"right update {t}", R[t+1]-nextR)
    eq("final halt", state[T][M.halt]-1)
    assert len(names) == (3*M.m+6)*T+3*S+M.m+4
    assert len(equations) == (4*M.m+7)*T+3*S+2*M.m+7
    return Certificate(M,T,S,names,equations)


def candidate_witness(C: Certificate, right_input: int) -> tuple[int, dict[str,int]]:
    """Return the unique deterministic candidate, also for rejecting bounds.

    C.evaluate(n,w) is zero precisely when the machine halts by C.T.
    """
    M,T,S = C.machine,C.T,C.S
    natural(right_input, "right_input")
    if right_input >= 1 << S:
        raise ValueError("input does not fit the selected S-bit bound")
    w: dict[str,int] = {}
    digits = [(right_input >> i) & 1 for i in range(S)]
    for i,digit in enumerate(digits):
        w[f"d_{i}"] = digit
    x = y = 0
    w["x_0"] = w["y_0"] = 0
    for i in range(S):
        x = 2*x+digits[S-1-i]; y = 4*y+digits[S-1-i]
        w[f"x_{i+1}"] = x; w[f"y_{i+1}"] = y
    q,left,right = M.start,0,right_input
    for t in range(T+1):
        w[f"L_{t}"] = left; w[f"R_{t}"] = right
        for p in range(M.m):
            w[f"s_{t}_{p}"] = int(p == q)
        if t == T:
            break
        a,b,A,B = left & 1,right & 1,left >> 1,right >> 1
        for name,value in zip(("a","b","A","B"),(a,b,A,B)):
            w[f"{name}_{t}"] = value
        for p in range(M.m):
            for read in (0,1):
                w[f"e_{t}_{p}_{read}"] = int(p == q and read == b)
        q,left,right = M.step(q,left,right)
    assert set(w) == set(C.variables)
    return M.encode(M.start,0,right_input), w
