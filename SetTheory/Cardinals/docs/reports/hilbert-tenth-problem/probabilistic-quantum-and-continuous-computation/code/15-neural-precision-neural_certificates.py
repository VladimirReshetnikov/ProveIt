#!/usr/bin/env python3
"""Exact certificate compilers used in 'Precision Is Memory'.

Python 3.10+, standard library only. All coefficient arithmetic is integral;
all neural evaluations use fractions.Fraction. No numerical optimizer or
floating-point test is used. This is executable mathematics, not a Lean proof.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from math import lcm
from typing import Mapping, Sequence


@dataclass
class Poly:
    """Sparse integer polynomial; a monomial is a sorted tuple of names."""
    terms: dict[tuple[str, ...], int] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self.terms = {tuple(sorted(m)): c for m, c in self.terms.items() if c}
        if any(not isinstance(c, int) for c in self.terms.values()):
            raise TypeError("Polynomial coefficients must be integers")

    @staticmethod
    def var(name: str) -> Poly:
        return Poly({(name,): 1})

    @staticmethod
    def const(value: int) -> Poly:
        return Poly({(): value})

    @staticmethod
    def coerce(value: Poly | int) -> Poly:
        return value if isinstance(value, Poly) else Poly.const(value)

    def __add__(self, other: Poly | int) -> Poly:
        d = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            d[m] = d.get(m, 0) + c
        return Poly(d)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: Poly | int) -> Poly:
        d: dict[tuple[str, ...], int] = {}
        for m, c in self.terms.items():
            for n, e in self.coerce(other).terms.items():
                key = tuple(sorted(m + n))
                d[key] = d.get(key, 0) + c * e
        return Poly(d)

    __rmul__ = __mul__

    def square(self) -> Poly:
        return self * self

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Mapping[str, int | Fraction]) -> int | Fraction:
        result: int | Fraction = 0
        for monomial, coefficient in self.terms.items():
            term: int | Fraction = coefficient
            for name in monomial:
                term *= values[name]
            result += term
        return result

    def json_terms(self) -> list[dict]:
        return [{"coefficient": c, "monomial": list(m)}
                for m, c in sorted(self.terms.items(), key=lambda p: (len(p[0]), p[0]))]


@dataclass
class Certificate:
    variables: list[str] = field(default_factory=list)
    squares: list[tuple[str, Poly]] = field(default_factory=list)
    products: list[tuple[str, str]] = field(default_factory=list)

    def variable(self, name: str) -> Poly:
        if name in self.variables:
            raise ValueError(f"Duplicate variable: {name}")
        self.variables.append(name)
        return Poly.var(name)

    def residual(self, name: str, expression: Poly) -> None:
        self.squares.append((name, expression))

    def evaluate(self, values: Mapping[str, int]) -> int:
        if set(values) != set(self.variables):
            raise ValueError("Witness keys must match the certificate variables")
        if any(not isinstance(v, int) or isinstance(v, bool) or v < 0
               for v in values.values()):
            raise ValueError("All witnesses must be natural numbers")
        return int(sum(p.evaluate(values) ** 2 for _, p in self.squares)
                   + sum(values[a] * values[b] for a, b in self.products))

    def polynomial(self) -> Poly:
        p = Poly.const(0)
        for _, r in self.squares:
            p += r.square()
        for a, b in self.products:
            p += Poly.var(a) * Poly.var(b)
        return p

    def to_json(self) -> dict:
        polynomial = self.polynomial()
        return {"domain": "nonnegative integers", "variables": self.variables,
                "degree": polynomial.degree,
                "squared_residuals": [
                    {"name": name, "terms": p.json_terms()}
                    for name, p in self.squares],
                "unsquared_nonnegative_products": self.products,
                "expanded_polynomial": polynomial.json_terms()}


def clip(x: Fraction | int) -> Fraction:
    return min(Fraction(1), max(Fraction(0), Fraction(x)))


def clamp_witness(D: int, U: int) -> tuple[int, int, int, int]:
    if D <= 0:
        raise ValueError("D must be positive")
    y = min(D, max(0, U))
    return y, D - y, max(-U, 0), max(U - D, 0)


def clamp_value(D: int, U: int, y: int, z: int, a: int, b: int) -> int:
    if D <= 0 or min(y, z, a, b) < 0:
        raise ValueError("Wrong domain for the clamp lemma")
    return (y + z - D) ** 2 + (y - U - a + b) ** 2 + y * a + z * b


@dataclass(frozen=True)
class RationalNetwork:
    A: tuple[tuple[int, ...], ...]
    b: tuple[int, ...]
    B: int

    def __post_init__(self) -> None:
        n = len(self.b)
        if n == 0 or len(self.A) != n or any(len(row) != n for row in self.A):
            raise ValueError("A must be a nonempty square matrix matching b")
        if self.B < 1:
            raise ValueError("The denominator B must be positive")
        if any(not isinstance(v, int) for row in self.A for v in row):
            raise TypeError("A must be integral")
        if any(not isinstance(v, int) for v in self.b):
            raise TypeError("b must be integral")

    @property
    def n(self) -> int:
        return len(self.b)

    def step(self, x: Sequence[Fraction]) -> tuple[Fraction, ...]:
        if len(x) != self.n:
            raise ValueError("State dimension mismatch")
        return tuple(clip((sum(a * v for a, v in zip(row, x)) + bi) / self.B)
                     for row, bi in zip(self.A, self.b))


def compile_trace(net: RationalNetwork, p: Sequence[int], D0: int, T: int,
                  halt: int | None = None, first_hit: bool = False
                  ) -> tuple[Certificate, dict[str, int], list[tuple[Fraction, ...]]]:
    """Compile T steps and return the deterministic arithmetic witness.

    When an optional acceptance requirement fails, the returned assignment
    correctly has nonzero certificate value. It is not labeled a solution.
    """
    if D0 < 1 or T < 0 or len(p) != net.n or any(v < 0 or v > D0 for v in p):
        raise ValueError("Invalid initial state or time")
    if halt is not None and not 0 <= halt < net.n:
        raise ValueError("Invalid halt coordinate")
    if first_hit and halt is None:
        raise ValueError("first_hit requires a halt coordinate")
    cert = Certificate()
    witness: dict[str, int] = {}
    states = [tuple(Fraction(v, D0) for v in p)]
    Xprev = [Poly.const(v) for v in p]
    ints_prev = list(p)
    Ds = [D0]
    all_X = [Xprev]
    all_ints = [ints_prev]
    for t in range(T):
        D, Dnext = Ds[-1], Ds[-1] * net.B
        curr, ints_curr = [], []
        for i in range(net.n):
            names = [f"{prefix}_{t+1}_{i}" for prefix in ("X", "C", "L", "H")]
            X, C, L, H = [cert.variable(name) for name in names]
            U = sum((a * x for a, x in zip(net.A[i], Xprev)), Poly.const(net.b[i] * D))
            ui = sum(a * x for a, x in zip(net.A[i], ints_prev)) + net.b[i] * D
            vals = clamp_witness(Dnext, ui)
            witness.update(zip(names, vals))
            cert.residual(f"bound_{t}_{i}", X + C - Dnext)
            cert.residual(f"transition_{t}_{i}", X - U - L + H)
            cert.products += [(names[0], names[2]), (names[1], names[3])]
            curr.append(X)
            ints_curr.append(vals[0])
        Xprev, ints_prev = curr, ints_curr
        Ds.append(Dnext)
        all_X.append(curr)
        all_ints.append(ints_curr)
        states.append(tuple(Fraction(x, Dnext) for x in ints_curr))
    if halt is not None:
        cert.residual("accept_at_T", Xprev[halt] - Ds[-1])
    if first_hit:
        assert halt is not None
        for t in range(T):
            name = f"s_{t}"
            s = cert.variable(name)
            cert.residual(f"not_yet_accept_{t}", Ds[t] - all_X[t][halt] - 1 - s)
            witness[name] = max(0, Ds[t] - all_ints[t][halt] - 1)
    return cert, witness, states


def projective_example(Q: int = 12) -> tuple[Certificate, dict[str, int]]:
    """x' = clip(2x-1/2), terminal x'=1/3. A zero needs Q divisible by 12."""
    if Q < 1:
        raise ValueError("Q must be positive")
    cert = Certificate()
    X0, C0, X1, C1, L, H, r = [cert.variable(name)
                                 for name in ("X0", "C0", "X1", "C1", "L", "H", "r")]
    q = r + 1
    cert.residual("initial_bound", X0 + C0 - q)
    cert.residual("terminal_bound", X1 + C1 - q)
    cert.residual("transition", 2 * X1 - 4 * X0 + q - L + H)
    cert.residual("target", 3 * X1 - q)
    cert.products = [("X1", "L"), ("C1", "H")]
    values = dict(X0=5 * Q // 12, C0=Q - 5 * Q // 12,
                  X1=Q // 3, C1=Q - Q // 3, L=0, H=0, r=Q-1)
    return cert, values


@dataclass(frozen=True)
class Wire:
    name: str
    op: str
    inputs: tuple[str, ...] = ()
    constant: int = 0


def circuit_values(wires: Sequence[Wire], inputs: Mapping[str, Fraction]
                   ) -> dict[str, Fraction]:
    values: dict[str, Fraction] = {}
    for w in wires:
        if w.name in values:
            raise ValueError("Repeated circuit wire")
        if w.op == "input":
            value = Fraction(inputs[w.name])
        elif w.op == "const":
            value = Fraction(w.constant)
        elif w.op in {"add", "sub", "mul"} and len(w.inputs) == 2:
            x, y = (values[name] for name in w.inputs)
            value = x + y if w.op == "add" else x - y if w.op == "sub" else x * y
        else:
            raise ValueError(f"Unsupported circuit operation: {w.op}")
        values[w.name] = value
    return values


def compactify_circuit(wires: Sequence[Wire], output: str
                       ) -> tuple[list[str], list[Poly]]:
    names = [w.name for w in wires]
    if len(set(names)) != len(names) or output not in names:
        raise ValueError("Circuit wire names must be unique and include the output")
    params = ["a_" + name for name in names] + ["v"]
    v = Poly.var("v")
    u = {name: 2 * Poly.var("a_" + name) - 1 for name in names}
    relations = []
    seen: set[str] = set()
    for w in wires:
        if any(i not in seen for i in w.inputs):
            raise ValueError("Circuit must be acyclic and topologically ordered")
        if w.op == "const":
            relations.append(u[w.name] - w.constant * v)
        elif w.op in {"add", "sub", "mul"}:
            if len(w.inputs) != 2:
                raise ValueError("Binary gate expected")
            x, y = (u[name] for name in w.inputs)
            r = u[w.name] - x - y if w.op == "add" else (
                u[w.name] - x + y if w.op == "sub" else v * u[w.name] - x * y)
            relations.append(r)
        elif w.op != "input":
            raise ValueError("Unsupported circuit gate")
        seen.add(w.name)
    relations.append(u[output])
    return params, relations


@dataclass(frozen=True)
class Parameter:
    name: str


@dataclass(frozen=True)
class Node:
    name: str
    layer: int
    edges: tuple[tuple[str, Fraction | Parameter], ...]
    bias: Fraction = Fraction(0)


@dataclass
class ParameterNetwork:
    parameters: list[str]
    nodes: list[Node]
    zero_output: str
    positive_output: str

    def evaluate(self, theta: Mapping[str, Fraction]) -> dict[str, Fraction]:
        if set(theta) != set(self.parameters) or any(not 0 <= x <= 1 for x in theta.values()):
            raise ValueError("Parameters must be exactly the named rational values in [0,1]")
        values = {"one": Fraction(1)}
        for node in self.nodes:
            z = node.bias
            for source, weight in node.edges:
                coefficient = theta[weight.name] if isinstance(weight, Parameter) else weight
                z += coefficient * values[source]
            values[node.name] = clip(z)
        return values


def quadratic_relations_network(parameters: Sequence[str], relations: Sequence[Poly],
                                positive_parameter: str = "v") -> ParameterNetwork:
    """Four layers, bounded tied parameters, output zero iff all relations vanish."""
    params = list(parameters)
    if len(set(params)) != len(params) or positive_parameter not in params:
        raise ValueError("Invalid parameter list")
    products = sorted({m for r in relations for m in r.terms if len(m) == 2})
    if any(r.degree > 2 for r in relations):
        raise ValueError("Only quadratic relations are supported")
    if any(name not in params for r in relations for m in r.terms for name in m):
        raise ValueError("Unknown parameter in relation")
    nodes: list[Node] = []
    first, copied = {}, {}
    for i, name in enumerate(params):
        first[name], copied[name] = f"first_{i}", f"copy_{i}"
        nodes.append(Node(first[name], 1, (("one", Parameter(name)),)))
    for name in params:
        nodes.append(Node(copied[name], 2, ((first[name], Fraction(1)),)))
    product_nodes = {}
    for k, (a, b) in enumerate(products):
        name = f"product_{k}"
        product_nodes[(a, b)] = name
        nodes.append(Node(name, 2, ((first[b], Parameter(a)),)))
    detector_names = []
    for k, r in enumerate(relations):
        for sign, tag in ((1, "plus"), (-1, "minus")):
            edges, bias = [], 0
            for m, c in r.terms.items():
                if len(m) == 0:
                    bias = sign * c
                else:
                    source = copied[m[0]] if len(m) == 1 else product_nodes[m]
                    edges.append((source, Fraction(sign * c)))
            name = f"residual_{k}_{tag}"
            nodes.append(Node(name, 3, tuple(edges), Fraction(bias)))
            detector_names.append(name)
    nodes.append(Node("positive_copy", 3, ((copied[positive_parameter], Fraction(1)),)))
    nodes.append(Node("zero_output", 4, tuple((name, Fraction(1)) for name in detector_names)))
    nodes.append(Node("positive_output", 4, (("positive_copy", Fraction(1)),)))
    return ParameterNetwork(params, nodes, "zero_output", "positive_output")


def quartic_synthesis_certificate(net: ParameterNetwork, theta: Mapping[str, Fraction]
                                  ) -> tuple[Certificate, dict[str, int], int, dict[str, Fraction]]:
    """Compile a feedforward parameter network, returning a rational evaluation lift.

    The certificate itself is independent of theta. Theta is used only to
    construct an example assignment; feasibility is existential over all its
    integer witnesses. Fixed edges and biases may be arbitrary rationals.
    """
    states = net.evaluate(theta)
    Qvalue = lcm(*(x.denominator for x in list(theta.values()) + list(states.values())))
    B = lcm(*(w.denominator for node in net.nodes for _, w in node.edges
              if isinstance(w, Fraction)), *(node.bias.denominator for node in net.nodes))
    cert = Certificate()
    r = cert.variable("scale_minus_one")
    Q = r + 1
    witness = {"scale_minus_one": Qvalue - 1}
    Theta = {}
    for j, name in enumerate(net.parameters):
        a, c = f"theta_{j}", f"theta_complement_{j}"
        Theta[name] = cert.variable(a)
        C = cert.variable(c)
        cert.residual(f"parameter_bound_{j}", Theta[name] + C - Q)
        witness[a] = int(theta[name] * Qvalue)
        witness[c] = Qvalue - witness[a]
    X = {"one": Q}
    xv = {"one": Qvalue}
    for j, node in enumerate(net.nodes):
        names = [f"{tag}_{j}" for tag in ("X", "C", "L", "H")]
        x, c, low, high = [cert.variable(name) for name in names]
        U = int(B * node.bias) * Q.square()
        ui = int(B * node.bias) * Qvalue ** 2
        for source, weight in node.edges:
            if isinstance(weight, Parameter):
                U += B * Theta[weight.name] * X[source]
                ui += B * int(theta[weight.name] * Qvalue) * xv[source]
            else:
                U += int(B * weight) * Q * X[source]
                ui += int(B * weight) * Qvalue * xv[source]
        cert.residual(f"state_bound_{j}", x + c - Q)
        cert.residual(f"gate_{j}", B * Q * x - U - low + high)
        cert.products.extend([(names[0], names[2]), (names[1], names[3])])
        xi = int(states[node.name] * Qvalue)
        witness.update(zip(names, (xi, Qvalue - xi, max(-ui, 0), max(ui - B * Qvalue**2, 0))))
        X[node.name], xv[node.name] = x, xi
    cert.residual("zero_target", X[net.zero_output])
    s = cert.variable("positive_slack")
    cert.residual("positive_target", X[net.positive_output] - 1 - s)
    witness["positive_slack"] = max(0, xv[net.positive_output] - 1)
    return cert, witness, Qvalue, states


def stack_encode(bits: Sequence[int]) -> Fraction:
    if any(bit not in (0, 1) for bit in bits):
        raise ValueError("A binary word is required")
    return sum((Fraction(2 * bit + 1, 4 ** (i + 1)) for i, bit in enumerate(bits)), Fraction(0))


def stack_top(x: Fraction) -> Fraction:
    return clip(4 * x - 2)


def stack_pop(x: Fraction) -> Fraction:
    return clip(4 * x - 1 - 2 * stack_top(x))


def stack_push(bit: int, x: Fraction) -> Fraction:
    if bit not in (0, 1):
        raise ValueError("A binary bit is required")
    return (x + 1 + 2 * bit) / 4


def common_denominator(state: Sequence[Fraction]) -> int:
    return lcm(*(x.denominator for x in state))
