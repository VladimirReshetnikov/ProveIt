#!/usr/bin/env python3
"""Exact cyclotomic tensors and canonical quadratic Diophantine certificates.

Python >= 3.10, standard library only. No floating-point arithmetic is used.
Variables of every exported polynomial range over the nonnegative integers.
The prototype constructs the certificate and its canonical witness together;
this is not a polynomial-time general-purpose quantum simulator.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Iterable
import json

Cyclo = tuple[int, int, int, int]  # coefficients of 1,w,w^2,w^3; w^4=-1
ZERO: Cyclo = (0, 0, 0, 0)
ONE: Cyclo = (1, 0, 0, 0)


def cadd(a: Cyclo, b: Cyclo) -> Cyclo:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def cneg(a: Cyclo) -> Cyclo:
    return tuple(-x for x in a)  # type: ignore[return-value]


def cmul(a: Cyclo, b: Cyclo) -> Cyclo:
    c = [0] * 4
    for i in range(4):
        for j in range(4):
            c[(i+j) % 4] += (1 if i+j < 4 else -1) * a[i] * b[j]
    return tuple(c)  # type: ignore[return-value]


def cconj(a: Cyclo) -> Cyclo:
    return (a[0], -a[3], -a[2], -a[1])


def wpow(k: int) -> Cyclo:
    k %= 8
    a = [0] * 4
    a[k % 4] = 1 if k < 4 else -1
    return tuple(a)  # type: ignore[return-value]


def real_coeff(a: Cyclo) -> tuple[int, int]:
    if a[2] != 0 or a[3] != -a[1]:
        raise ValueError(f"Not real in Z[w]: {a}")
    return a[0], a[1]


def sign_sqrt2(p: int, q: int) -> int:
    """Exact sign of p + q*sqrt(2)."""
    if not p and not q:
        return 0
    if p >= 0 and q >= 0:
        return 1
    if p <= 0 and q <= 0:
        return -1
    d = p*p - 2*q*q
    return (1 if d > 0 else -1) if p >= 0 else (1 if d < 0 else -1)


class Poly:
    """Sparse integer polynomial; a monomial is a sorted tuple of indices."""
    def __init__(self, terms: dict[tuple[int, ...], int] | None = None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def const(n: int) -> Poly:
        return Poly({(): n})

    @staticmethod
    def var(i: int) -> Poly:
        return Poly({(i,): 1})

    def __add__(self, other: Poly | int) -> Poly:
        other = other if isinstance(other, Poly) else Poly.const(other)
        t = dict(self.terms)
        for m, c in other.terms.items():
            t[m] = t.get(m, 0) + c
        return Poly(t)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + (-other if isinstance(other, Poly) else -other)

    def __rsub__(self, other: int) -> Poly:
        return -self + other

    def __mul__(self, other: Poly | int) -> Poly:
        other = other if isinstance(other, Poly) else Poly.const(other)
        t: dict[tuple[int, ...], int] = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                key = tuple(sorted(m+n))
                t[key] = t.get(key, 0) + c*d
        return Poly(t)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: list[int]) -> int:
        total = 0
        for m, c in self.terms.items():
            for i in m:
                c *= values[i]
            total += c
        return total

    def encoded(self) -> list[dict]:
        return [{"coefficient": c, "variables": list(m)}
                for m, c in sorted(self.terms.items())]


@dataclass(frozen=True)
class IntWire:
    pos: int
    neg: int
    value: int

    @property
    def expr(self) -> Poly:
        return Poly.var(self.pos) - Poly.var(self.neg)


RingWire = tuple[IntWire, IntWire, IntWire, IntWire]


class Certificate:
    def __init__(self):
        self.names: list[str] = []
        self.witness: list[int] = []
        self.constraints: list[Poly] = []
        self.constants: dict[int, IntWire] = {}
        self.arithmetic_gates = 0

    def natural(self, name: str, value: int) -> int:
        if value < 0:
            raise ValueError("Natural witness must be nonnegative")
        i = len(self.names)
        self.names.append(f"{name}_{i}")
        self.witness.append(value)
        return i

    def equation(self, p: Poly) -> None:
        if p.degree > 2:
            raise ValueError(f"Constraint has degree {p.degree}, not <=2")
        self.constraints.append(p)

    def wire(self, value: int, name: str = "z") -> IntWire:
        p = self.natural(name + "p", max(value, 0))
        n = self.natural(name + "m", max(-value, 0))
        self.equation(Poly.var(p) * Poly.var(n))
        return IntWire(p, n, value)

    def const(self, value: int) -> IntWire:
        if value not in self.constants:
            w = self.wire(value, "constant")
            self.equation(w.expr - value)
            self.constants[value] = w
        return self.constants[value]

    def add(self, a: IntWire, b: IntWire) -> IntWire:
        z = self.wire(a.value + b.value, "add")
        self.equation(z.expr - a.expr - b.expr)
        self.arithmetic_gates += 1
        return z

    def sub(self, a: IntWire, b: IntWire) -> IntWire:
        z = self.wire(a.value - b.value, "sub")
        self.equation(z.expr - a.expr + b.expr)
        self.arithmetic_gates += 1
        return z

    def mul(self, a: IntWire, b: IntWire) -> IntWire:
        z = self.wire(a.value * b.value, "mul")
        self.equation(z.expr - a.expr*b.expr)
        self.arithmetic_gates += 1
        return z

    def neg(self, a: IntWire) -> IntWire:
        return self.sub(self.const(0), a)

    def ring_const(self, c: Cyclo) -> RingWire:
        return tuple(self.const(x) for x in c)  # type: ignore[return-value]

    def ring_add(self, a: RingWire, b: RingWire) -> RingWire:
        return tuple(self.add(x, y) for x, y in zip(a, b))  # type: ignore[return-value]

    def ring_mul(self, a: RingWire, b: RingWire) -> RingWire:
        terms: list[list[tuple[IntWire, int]]] = [[] for _ in range(4)]
        for i in range(4):
            for j in range(4):
                terms[(i+j) % 4].append((self.mul(a[i], b[j]),
                                             1 if i+j < 4 else -1))
        out = []
        for row in terms:
            # Each row starts with the positive term a[0]*b[k].
            z, sign = row[0]
            assert sign == 1
            for term, sign in row[1:]:
                z = self.add(z, term) if sign == 1 else self.sub(z, term)
            out.append(z)
        return tuple(out)  # type: ignore[return-value]

    def nonnegative(self, a: IntWire) -> int:
        """Unique Boolean b satisfying b=1 iff the signed integer a>=0."""
        b_value = int(a.value >= 0)
        b = self.natural("nonnegative", b_value)
        s = self.natural("slack", max(-a.value-1, 0))
        B, S, M = Poly.var(b), Poly.var(s), Poly.var(a.neg)
        self.equation(B*(B-1))
        self.equation(B*M)
        self.equation(M-(1-B)*(S+1))
        self.equation(B*S)
        return b

    def sqrt2_nonnegative(self, p: IntWire, q: IntWire) -> int:
        """Unique b=1 iff p+q*sqrt(2)>=0. All constraints are quadratic."""
        pp = self.mul(p, p)
        qq = self.mul(q, q)
        twice = self.mul(self.const(2), qq)
        d = self.sub(pp, twice)
        nd = self.neg(d)
        alpha, beta = self.nonnegative(p), self.nonnegative(q)
        gamma, delta = self.nonnegative(d), self.nonnegative(nd)
        A, B, G, D = map(Poly.var, (alpha, beta, gamma, delta))
        av, bv = self.witness[alpha], self.witness[beta]
        e = self.natural("mixed_e", av*(1-bv))
        f = self.natural("mixed_f", (1-av)*bv)
        out = self.natural("algebraic_nonnegative", int(sign_sqrt2(p.value,q.value)>=0))
        E, F, O = map(Poly.var, (e, f, out))
        self.equation(E-A*(1-B))
        self.equation(F-(1-A)*B)
        self.equation(O-A*B-E*G-F*D)
        return out

    def require_probability_gt(self, result: RingWire, h: int,
                               numerator: int, denominator: int) -> None:
        if h < 0 or numerator < 0 or denominator <= 0:
            raise ValueError("Require h,u>=0 and v>0")
        a, b, c, d = result
        self.equation(c.expr)
        self.equation(d.expr+b.expr)
        p = self.sub(self.mul(self.const(denominator), a),
                     self.const(numerator*(1 << h)))
        q = self.mul(self.const(denominator), b)
        # x>0 iff -x is NOT nonnegative. Avoid approximate comparisons.
        test = self.sqrt2_nonnegative(self.neg(p), self.neg(q))
        self.equation(Poly.var(test))

    def valid(self, witness: list[int] | None = None) -> bool:
        v = self.witness if witness is None else witness
        return (len(v) == len(self.names) and all(isinstance(x,int) and x>=0 for x in v)
                and all(p.evaluate(v)==0 for p in self.constraints))

    def sum_of_squares(self) -> Poly:
        out = Poly()
        for p in self.constraints:
            out = out + p*p
        return out

    def export(self, path: str, *, expanded: bool = False,
               metadata: dict | None = None) -> dict:
        info = {"domain": "nonnegative integers", "variables": self.names,
                "witness": self.witness,
                "quadratic_constraints": [p.encoded() for p in self.constraints],
                "single_polynomial": "sum of squares of quadratic_constraints",
                "max_constraint_degree": max((p.degree for p in self.constraints), default=0),
                "valid_witness": self.valid()}
        if metadata is not None:
            info["metadata"] = metadata
        if expanded:
            p = self.sum_of_squares()
            info["expanded_quartic"] = p.encoded()
            info["quartic_degree"] = p.degree
        with open(path, "w", encoding="utf-8") as f:
            json.dump(info, f, indent=2)
            f.write("\n")
        return info


@dataclass(frozen=True)
class Gate:
    name: str
    qubits: tuple[int, ...]

    def validate(self, n: int) -> None:
        arities = {"H":1,"T":1,"TDG":1,"S":1,"X":1,"Z":1,
                   "CX":2,"CZ":2,"CCX":3}
        if self.name not in arities or len(self.qubits)!=arities[self.name]:
            raise ValueError(f"Invalid gate {self}")
        if len(set(self.qubits))!=len(self.qubits) or any(q<0 or q>=n for q in self.qubits):
            raise ValueError(f"Invalid qubits {self}")


def gate_entry(g: Gate, x: tuple[int, ...], y: tuple[int, ...]) -> Cyclo:
    if g.name == "H":
        return (-1,0,0,0) if x[0] and y[0] else ONE
    out = list(x)
    phase = ONE
    if g.name == "X": out[0] ^= 1
    elif g.name == "CX": out[1] ^= x[0]
    elif g.name == "CCX": out[2] ^= x[0] & x[1]
    elif g.name == "CZ": phase = (-1,0,0,0) if x[0] and x[1] else ONE
    elif g.name in {"T","TDG","S","Z"}:
        phase = wpow({"T":1,"TDG":-1,"S":2,"Z":4}[g.name]*x[0])
    else: raise ValueError(f"Unknown gate {g.name}")
    return phase if tuple(out)==y else ZERO


def dense_state(n: int, gates: Iterable[Gate], initial: int=0) -> tuple[list[Cyclo], int]:
    if n < 1 or not 0 <= initial < (1 << n):
        raise ValueError("Invalid initial state")
    state = [ZERO]*(1 << n)
    state[initial] = ONE
    h = 0
    for g in gates:
        g.validate(n)
        new = [ZERO]*(1 << n)
        for i, amp in enumerate(state):
            if amp == ZERO: continue
            x = tuple((i >> q)&1 for q in g.qubits)
            for y in product((0,1), repeat=len(g.qubits)):
                entry = gate_entry(g,x,y)
                if entry == ZERO: continue
                j = i
                for q,b in zip(g.qubits,y): j = (j & ~(1 << q)) | (b << q)
                new[j] = cadd(new[j], cmul(entry,amp))
        state = new
        h += g.name == "H"
    return state, h


def probability_numerator(state: list[Cyclo], measured: dict[int,int]) -> Cyclo:
    total = ZERO
    for j,a in enumerate(state):
        if all((j >> q)&1 == b for q,b in measured.items()):
            total = cadd(total,cmul(a,cconj(a)))
    return total


@dataclass
class Tensor:
    edges: tuple[int, ...]
    data: dict[tuple[int, ...], Cyclo]


def probability_network(n: int, gates: list[Gate], initial: int=0,
                        measured: dict[int,int] | None=None) -> tuple[list[Tensor],int]:
    if n < 1 or not 0 <= initial < 1 << n:
        raise ValueError("Invalid initial state")
    measured = measured or {}
    if any(q<0 or q>=n or b not in (0,1) for q,b in measured.items()):
        raise ValueError("Invalid measurement")
    tensors: list[Tensor] = []
    edge = 0
    ends: list[list[int]] = []
    for bra in (False,True):
        current=[]
        for q in range(n):
            current.append(edge); bit=(initial >> q)&1
            tensors.append(Tensor((edge,),{(b,):ONE if b==bit else ZERO for b in (0,1)}))
            edge += 1
        for g in gates:
            g.validate(n)
            ins=tuple(current[q] for q in g.qubits)
            outs=tuple(range(edge,edge+len(g.qubits))); edge+=len(g.qubits)
            table={}
            for x in product((0,1),repeat=len(g.qubits)):
                for y in product((0,1),repeat=len(g.qubits)):
                    z=gate_entry(g,x,y)
                    table[x+y]=cconj(z) if bra else z
            tensors.append(Tensor(ins+outs,table))
            for q,e in zip(g.qubits,outs): current[q]=e
        ends.append(current)
    for q in range(n):
        table={(x,y): ONE if x==y and (q not in measured or x==measured[q]) else ZERO
               for x in (0,1) for y in (0,1)}
        tensors.append(Tensor((ends[0][q],ends[1][q]),table))
    return tensors, sum(g.name=="H" for g in gates)


def validate_network(tensors: list[Tensor]) -> None:
    if not tensors: raise ValueError("A network must have at least one tensor")
    counts: dict[int,int]={}
    for t in tensors:
        if len(t.edges)!=len(set(t.edges)): raise ValueError("Self loops are not supported")
        if set(t.data)!=set(product((0,1),repeat=len(t.edges))):
            raise ValueError("Tables must be complete binary tensors")
        for e in t.edges: counts[e]=counts.get(e,0)+1
    if any(v!=2 for v in counts.values()):
        raise ValueError("Every edge must occur at exactly two tensors")


def contract(tensors: list[Tensor], cert: Certificate | None=None,
             *, order: str="greedy") -> tuple[Cyclo | RingWire,dict]:
    """Contract all shared indices at each merge. Disconnected products are allowed."""
    validate_network(tensors)
    if order not in {"greedy","queue"}: raise ValueError("Unknown contraction order")
    nodes=[]
    for t in tensors:
        nodes.append((t.edges,{k:cert.ring_const(v) if cert else v for k,v in t.data.items()}))
    stats={"leaf_entries":sum(len(t.data) for t in tensors),"term_products":0,
           "output_entries":0,"merge_union_width":0,"merges":0}
    while len(nodes)>1:
        if order=="queue": i,j=0,1
        else:
            _,_,i,j=min((len(set(a[0])|set(b[0])),len(set(a[0])^set(b[0])),i,j)
                        for i,a in enumerate(nodes) for j,b in enumerate(nodes) if i<j)
        ae,ad=nodes[i]; be,bd=nodes[j]
        shared=tuple(sorted(set(ae)&set(be)))
        out_edges=tuple(sorted(set(ae)^set(be)))
        stats["merge_union_width"]=max(stats["merge_union_width"],len(set(ae)|set(be)))
        stats["term_products"]+=1 << len(set(ae)|set(be))
        stats["output_entries"]+=1 << len(out_edges)
        stats["merges"]+=1
        table={}
        for out in product((0,1),repeat=len(out_edges)):
            d=dict(zip(out_edges,out)); acc=None
            for middle in product((0,1),repeat=len(shared)):
                d.update(zip(shared,middle))
                a=ad[tuple(d[e] for e in ae)]; b=bd[tuple(d[e] for e in be)]
                term=cert.ring_mul(a,b) if cert else cmul(a,b)
                if acc is None: acc=term
                else: acc=cert.ring_add(acc,term) if cert else cadd(acc,term)
            table[out]=acc
        nodes=[x for k,x in enumerate(nodes) if k not in (i,j)]+[(out_edges,table)]
    if nodes[0][0]: raise AssertionError("Contraction did not close")
    return nodes[0][1][()],stats


def branch_sum(n: int, edges: list[tuple[int,int]], outcome: tuple[int,...],
               angles: tuple[int,...]) -> Cyclo:
    """Full equatorial-measurement graph-state branch amplitude numerator.

    The physical amplitude is this result divided by 2**n. Angles are k*pi/4.
    For an adaptive branch, angles must already be evaluated on its prefixes.
    """
    if len(outcome)!=n or len(angles)!=n or any(b not in (0,1) for b in outcome):
        raise ValueError("Invalid branch")
    total=ZERO
    for x in product((0,1),repeat=n):
        phase=4*(sum(x[i]*x[j] for i,j in edges)+sum(s*b for s,b in zip(outcome,x)))
        phase-=sum(k*b for k,b in zip(angles,x))
        total=cadd(total,wpow(phase))
    return total


def branch_dense(n: int, edges: list[tuple[int,int]], outcome: tuple[int,...],
                 angles: tuple[int,...]) -> Cyclo:
    """Independent circuit realization: |+>, CZ, T**(-k), H, measure outcome."""
    gates=[Gate("H",(q,)) for q in range(n)]
    gates += [Gate("CZ",(i,j)) for i,j in edges]
    for q,k in enumerate(angles):
        gates += [Gate("TDG",(q,)) for _ in range(k%8)]
        gates.append(Gate("H",(q,)))
    state,h=dense_state(n,gates)
    assert h==2*n
    index=sum(b << q for q,b in enumerate(outcome))
    return state[index]


def graph_branch_network(n: int, edges: list[tuple[int,int]],
                         outcome: tuple[int,...], angles: tuple[int,...],
                         *, probability: bool=False) -> list[Tensor]:
    """Closed graph-state branch network using tensors of arity at most three.

    Returns the amplitude numerator A; with probability=True returns the
    doubled network for A*conj(A), whose physical denominator is 4**n.
    Adaptive angle rules must already have been evaluated on the fixed branch.
    """
    if n < 1 or len(outcome)!=n or len(angles)!=n or any(s not in (0,1) for s in outcome):
        raise ValueError("Invalid graph-state branch")
    normalized=[]
    for i,j in edges:
        if not 0 <= i < n or not 0 <= j < n or i==j:
            raise ValueError("Graph edges must join distinct valid vertices")
        normalized.append(tuple(sorted((i,j))))
    if len(set(normalized))!=len(normalized):
        raise ValueError("A simple graph cannot have repeated edges")
    tensors=[]
    incident=[[] for _ in range(n)]
    label=0
    for i in range(n):
        incident[i].append(label)
        tensors.append(Tensor((label,),{(x,):wpow((4*outcome[i]-angles[i])*x)
                                       for x in (0,1)}))
        label+=1
    for i,j in normalized:
        a,b=label,label+1;label+=2
        incident[i].append(a);incident[j].append(b)
        tensors.append(Tensor((a,b),{(x,y):wpow(4*x*y) for x in (0,1) for y in (0,1)}))

    def copy_tensor(indices: tuple[int,...]) -> None:
        tensors.append(Tensor(indices,{x:ONE if len(set(x))<=1 else ZERO
                                       for x in product((0,1),repeat=len(indices))}))

    for row in incident:
        k=len(row)
        if k<=3:
            copy_tensor(tuple(row))
        else:
            previous=label;label+=1
            copy_tensor((row[0],row[1],previous))
            for j in range(2,k-2):
                following=label;label+=1
                copy_tensor((previous,row[j],following))
                previous=following
            copy_tensor((previous,row[-2],row[-1]))
    if probability:
        conjugate=[Tensor(tuple(e+label for e in t.edges),
                          {x:cconj(a) for x,a in t.data.items()}) for t in tensors]
        tensors+=conjugate
    validate_network(tensors)
    return tensors
