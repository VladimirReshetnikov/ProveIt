#!/usr/bin/env python3
"""Exact, witness-free quadratic/quartic compilation of finite counter machines.

Python 3.10+, standard library only.  Polynomials are sparse integer dictionaries;
no numerical tolerances, symbolic-engine assumptions, or external solvers are used.
This is an executable construction, not a proof-assistant formalization.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Sequence
import json

Number = int | Fraction
Monomial = tuple[int, ...]

class Poly:
    """Sparse polynomial: a monomial is a sorted tuple of variable indices."""
    def __init__(self, nvars: int, terms: dict[Monomial, int] | None = None):
        if not isinstance(nvars, int) or nvars < 0:
            raise ValueError("Polynomial arity must be a nonnegative integer")
        self.nvars = nvars
        combined: dict[Monomial, int] = {}
        for monomial, coefficient in (terms or {}).items():
            if not isinstance(coefficient, int):
                raise ValueError("Polynomial coefficients must be integers")
            if any(not isinstance(i, int) for i in monomial):
                raise ValueError("Variable indices must be integers")
            key = tuple(sorted(monomial))
            combined[key] = combined.get(key, 0) + coefficient
        self.terms = {m: c for m, c in combined.items() if c}
        if any(i < 0 or i >= nvars for m in self.terms for i in m):
            raise ValueError("Variable index outside the polynomial's arity")

    @classmethod
    def constant(cls, nvars: int, c: int) -> Poly:
        return cls(nvars, {(): c})

    @classmethod
    def variable(cls, nvars: int, index: int) -> Poly:
        return cls(nvars, {(index,): 1})

    def _coerce(self, other: Poly | int) -> Poly:
        if isinstance(other, int):
            return Poly.constant(self.nvars, other)
        if not isinstance(other, Poly) or other.nvars != self.nvars:
            raise ValueError("Polynomial arities must agree")
        return other

    def __add__(self, other: Poly | int) -> Poly:
        other = self._coerce(other)
        out = dict(self.terms)
        for m, c in other.terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(self.nvars, out)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly(self.nvars, {m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + (-self._coerce(other))

    def __rsub__(self, other: Poly | int) -> Poly:
        return self._coerce(other) - self

    def __mul__(self, other: Poly | int) -> Poly:
        other = self._coerce(other)
        out: dict[Monomial, int] = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                key = tuple(sorted(m + n))
                out[key] = out.get(key, 0) + c * d
        return Poly(self.nvars, out)

    __rmul__ = __mul__

    def square(self) -> Poly:
        return self * self

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    @property
    def height(self) -> int:
        return max(map(abs, self.terms.values()), default=0)

    def evaluate(self, values: Sequence[Number]) -> Number:
        if len(values) != self.nvars:
            raise ValueError("Incorrect number of coordinates")
        total: Number = 0
        for monomial, coefficient in self.terms.items():
            term: Number = coefficient
            for i in monomial:
                term *= values[i]
            total += term
        return total

    def as_json(self, names: Sequence[str]) -> dict:
        if len(names) != self.nvars:
            raise ValueError("Incorrect number of variable names")
        return {"variables": list(names), "degree": self.degree,
                "coefficient_height": self.height,
                "terms": [{"coefficient": c, "monomial": [names[i] for i in m]}
                          for m, c in sorted(self.terms.items())]}

@dataclass(frozen=True)
class Edge:
    source: str
    target: str
    kind: str                 # inc, dec, zero, or nop
    counter: int | None = None

class Machine:
    """Natural counters; at most two syntactic outgoing edges per label.

    A state is (counter tuple, one-hot incoming-edge tuple).  Edge 0 is the
    artificial initial edge, from a fresh label '*' to the start label.
    """
    def __init__(self, counters: int, start: str, edges: Iterable[Edge],
                 marked: Iterable[str] = ()):
        if counters < 1 or start == "*":
            raise ValueError("Need positive counter count and an ordinary start label")
        real_edges = tuple(edges)
        for e in real_edges:
            if e.source == "*" or e.target == "*":
                raise ValueError("The label '*' is reserved")
            if e.kind not in {"inc", "dec", "zero", "nop"}:
                raise ValueError("Unknown edge kind")
            if e.kind == "nop":
                if e.counter is not None:
                    raise ValueError("A no-op has no counter")
            elif e.counter is None or not 0 <= e.counter < counters:
                raise ValueError("Invalid counter index")
        self.d = counters
        self.start = start
        self.edges = (Edge("*", start, "nop"),) + real_edges
        self.m = len(self.edges)
        self.dimension = self.d + self.m
        self.labels = sorted({start, "*"} | {e.source for e in self.edges}
                             | {e.target for e in self.edges})
        self.marked = frozenset(marked)
        if not self.marked.issubset(self.labels):
            raise ValueError("Marked labels must occur in the machine")
        self.outgoing = {q: tuple(i for i, e in enumerate(self.edges) if e.source == q)
                         for q in self.labels}
        if any(len(v) > 2 for v in self.outgoing.values()):
            raise ValueError("The machine is not binary branching")

    def onehot(self, edge: int) -> tuple[int, ...]:
        if not isinstance(edge, int) or not 0 <= edge < self.m:
            raise ValueError("Invalid edge index")
        return tuple(int(i == edge) for i in range(self.m))

    def initial(self, counters: Sequence[int] | None = None) -> tuple[int, ...]:
        x = tuple(counters if counters is not None else (0,) * self.d)
        if len(x) != self.d or any(not isinstance(v, int) or v < 0 for v in x):
            raise ValueError("Invalid initial counters")
        return x + self.onehot(0)

    def control(self, state: Sequence[int]) -> str | None:
        if len(state) != self.dimension or any(not isinstance(v, int) or v < 0 for v in state):
            return None
        bits = state[self.d:]
        if sum(bits) != 1:
            return None
        return self.edges[bits.index(1)].target

    def successors(self, state: Sequence[int]) -> tuple[tuple[int, ...], ...]:
        q = self.control(state)
        if q is None:
            return ()
        result = []
        for j in self.outgoing[q]:
            e = self.edges[j]
            x = list(state[:self.d])
            if e.kind == "zero" and x[e.counter] != 0:
                continue
            if e.kind == "dec":
                if x[e.counter] == 0:
                    continue
                x[e.counter] -= 1
            elif e.kind == "inc":
                x[e.counter] += 1
            result.append(tuple(x) + self.onehot(j))
        return tuple(result)

    def is_marked(self, state: Sequence[int]) -> bool:
        return self.control(state) in self.marked

    def compile(self) -> tuple[Poly, Poly, list[str]]:
        """Return P2, P4 and names in the order (x,b,y,c)."""
        D, m, d = self.dimension, self.m, self.d
        names = ([f"x{i}" for i in range(d)] + [f"b{j}" for j in range(m)]
                 + [f"y{i}" for i in range(d)] + [f"c{j}" for j in range(m)])
        variables = [Poly.variable(2 * D, i) for i in range(2 * D)]
        x, b = variables[:d], variables[d:D]
        y, c = variables[D:D+d], variables[D+d:]
        common = (sum(b) - 1).square() + (sum(c) - 1).square()
        for q in self.labels:
            incoming = sum((b[j] for j, e in enumerate(self.edges) if e.target == q),
                           Poly.constant(2*D, 0))
            outgoing = sum((c[j] for j, e in enumerate(self.edges) if e.source == q),
                           Poly.constant(2*D, 0))
            common += (incoming - outgoing).square()
        for i in range(d):
            delta = Poly.constant(2 * D, 0)
            for j, e in enumerate(self.edges):
                if e.counter == i and e.kind == "inc":
                    delta += c[j]
                elif e.counter == i and e.kind == "dec":
                    delta -= c[j]
            common += (y[i] - x[i] - delta).square()
        p2, p4 = common, common
        for j, e in enumerate(self.edges):
            if e.kind == "zero":
                product = c[j] * x[e.counter]
                p2 += product
                p4 += product.square()
        return p2, p4, names

    def direct_energy(self, old: Sequence[Number], new: Sequence[Number],
                      quartic: bool = False) -> Number:
        """Independent residual evaluator, also valid on rational coordinates."""
        if len(old) != self.dimension or len(new) != self.dimension:
            raise ValueError("Invalid state dimensions")
        x, b = old[:self.d], old[self.d:]
        y, c = new[:self.d], new[self.d:]
        value = (sum(b)-1)**2 + (sum(c)-1)**2
        for q in self.labels:
            u = sum(b[j] for j, e in enumerate(self.edges) if e.target == q)
            v = sum(c[j] for j, e in enumerate(self.edges) if e.source == q)
            value += (u-v)**2
        for i in range(self.d):
            change = sum((1 if e.kind == "inc" else -1) * c[j]
                         for j, e in enumerate(self.edges)
                         if e.counter == i and e.kind in {"inc", "dec"})
            value += (y[i]-x[i]-change)**2
        for j, e in enumerate(self.edges):
            if e.kind == "zero":
                z = c[j] * x[e.counter]
                value += z*z if quartic else z
        return value

    def description(self) -> dict:
        return {"counters": self.d, "start": self.start, "marked": sorted(self.marked),
                "state_dimension": self.dimension, "labels": self.labels,
                "edges_including_dummy": [e.__dict__ for e in self.edges]}


def countdown_machine() -> Machine:
    """Arbitrarily many finite marked visits, but no recurrent infinite run."""
    return Machine(1, "G", [Edge("G", "I", "nop"), Edge("G", "D", "nop"),
                             Edge("I", "G", "inc", 0), Edge("D", "A", "dec", 0),
                             Edge("D", "H", "zero", 0), Edge("A", "D", "nop")], {"A"})


def prefix_statistics(machine: Machine, horizon: int) -> dict:
    """Exact dynamic programming; visits count positions including time zero."""
    if horizon < 0:
        raise ValueError("Negative horizon")
    initial = machine.initial()
    frontier = {(initial, int(machine.is_marked(initial))): 1}
    maxima = [int(machine.is_marked(initial))]
    total_prefixes = [1]
    for _ in range(horizon):
        nxt: dict[tuple[tuple[int, ...], int], int] = {}
        for (state, visits), count in frontier.items():
            for successor in machine.successors(state):
                key = (successor, visits + int(machine.is_marked(successor)))
                nxt[key] = nxt.get(key, 0) + count
        frontier = nxt
        maxima.append(max((v for (_, v) in frontier), default=0))
        total_prefixes.append(sum(frontier.values()))
    return {"horizon": horizon, "maximum_visits_at_exact_horizon": maxima,
            "number_of_length_T_paths": total_prefixes}


def deadline_feasible(machine: Machine, deadlines: Sequence[int]) -> bool:
    """Check simultaneous first-k-visit deadlines by exhaustive finite exploration."""
    if not deadlines:
        return True
    if any(t < k+1 for k, t in enumerate(deadlines)) or list(deadlines) != sorted(deadlines):
        raise ValueError("Deadlines must be nondecreasing and g(k)>=k")
    initial = machine.initial()
    frontier = {(initial, int(machine.is_marked(initial)))}
    for t in range(1, deadlines[-1] + 1):
        frontier = {(s2, v + int(machine.is_marked(s2)))
                    for s, v in frontier for s2 in machine.successors(s)}
        required = max((k+1 for k, deadline in enumerate(deadlines) if deadline <= t), default=0)
        frontier = {(s, v) for s, v in frontier if v >= required}
        if not frontier:
            return False
    return bool(frontier)


def stack_encode(word: Sequence[int]) -> Fraction:
    """Finite binary stack; word[0] is its top. Digits are 1 and 3 in base 4."""
    if any(a not in (0, 1) for a in word):
        raise ValueError("Stack alphabet is {0,1}")
    value = Fraction(0)
    for a in reversed(word):
        value = (1 + 2*a + value) / 4
    return value


def stack_push(value: Fraction, symbol: int) -> Fraction:
    if symbol not in (0, 1) or not 0 <= value < 1:
        raise ValueError("Invalid encoded push")
    return (1 + 2*symbol + value) / 4


def stack_pop(value: Fraction) -> tuple[int, Fraction]:
    if Fraction(1,4) <= value < Fraction(1,2):
        return 0, 4*value - 1
    if Fraction(3,4) <= value < 1:
        return 1, 4*value - 3
    raise ValueError("Empty or invalid stack code")

if __name__ == "__main__":
    M = countdown_machine()
    p2, p4, names = M.compile()
    print(json.dumps({"machine": M.description(), "quadratic": p2.as_json(names),
                      "quartic": p4.as_json(names)}, indent=2))
