"""Exact low-degree tensor normalization for formulas of width at most three.

This module constructs a network; it does not implement a subexponential
tensor contractor. ``count_network_bruteforce`` is only a small-instance
verification oracle. All actual tensor entries are computed on demand.

For a normalized formula with L literal occurrences and occurrence degrees d_v,
``build_network(formula, B)`` uses exactly

    L + 2 * sum(max(d_v - 3, 0) // (B - 2) for v)

wires, for every integer B >= 3. Variable gadgets and their subdivision
vertices are equality tensors; original clauses have degree at most three.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Sequence


def _integer(value: object, name: str, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer at least {minimum}")
    return value


@dataclass(frozen=True)
class Formula:
    """A normalized formula using signed, one-based variable indices."""

    n_variables: int
    clauses: tuple[tuple[int, ...], ...]

    @property
    def literal_count(self) -> int:
        return sum(map(len, self.clauses))

    @property
    def occurrence_degrees(self) -> tuple[int, ...]:
        degrees = [0] * self.n_variables
        for clause in self.clauses:
            for literal in clause:
                degrees[abs(literal) - 1] += 1
        return tuple(degrees)

    @property
    def unused_variables(self) -> tuple[int, ...]:
        return tuple(v + 1 for v, d in enumerate(self.occurrence_degrees) if d == 0)

    def accepts(self, assignment: Sequence[int]) -> bool:
        if len(assignment) != self.n_variables or any(b not in (0, 1) for b in assignment):
            raise ValueError("assignment must give one Boolean bit per declared variable")
        return all(
            any(assignment[abs(lit) - 1] == int(lit > 0) for lit in clause)
            for clause in self.clauses
        )


def normalize_3cnf(n_variables: int, clauses: Iterable[Iterable[int]]) -> Formula:
    """Remove tautologies, repeated literals, and repeated whole clauses.

    Empty clauses are preserved and therefore still make the formula false.
    Declared variables, including variables absent after normalization, remain
    part of the counting problem. Inputs must have at most three literal slots
    per clause before normalization.
    """

    _integer(n_variables, "n_variables")
    normalized: set[tuple[int, ...]] = set()
    for raw_clause in clauses:
        clause = tuple(raw_clause)
        if len(clause) > 3:
            raise ValueError("input clause width exceeds three")
        for literal in clause:
            if isinstance(literal, bool) or not isinstance(literal, int):
                raise ValueError("literal must be a nonzero integer")
            if literal == 0 or abs(literal) > n_variables:
                raise ValueError("literal index is outside the declared variables")
        literals = set(clause)
        if any(-literal in literals for literal in literals):
            continue
        normalized.add(tuple(sorted(literals, key=lambda x: (abs(x), x < 0))))
    return Formula(n_variables, tuple(sorted(normalized)))


@dataclass(frozen=True)
class Tensor:
    index: int
    kind: str
    side: int
    edges: tuple[int, ...]
    signs: tuple[bool, ...] = ()
    variable: int | None = None

    def entry(self, bits: Sequence[int]) -> int:
        """Evaluate a 0/1 entry without constructing a tensor table."""

        if len(bits) != len(self.edges) or any(bit not in (0, 1) for bit in bits):
            raise ValueError("one Boolean bit is required per tensor port")
        if self.kind == "equality":
            # Construction never creates a zero-port equality tensor. The empty
            # convention below is nevertheless the ordinary empty product.
            return int(not bits or all(bit == bits[0] for bit in bits))
        if self.kind == "clause":
            if len(self.signs) != len(bits):
                raise ValueError("clause signs and ports disagree")
            return int(any(bit == int(sign) for bit, sign in zip(bits, self.signs)))
        raise ValueError(f"unknown tensor kind: {self.kind}")


@dataclass(frozen=True)
class Wire:
    left: int
    right: int
    variable: int
    internal: bool


@dataclass(frozen=True)
class Network:
    formula: Formula
    degree_cap: int
    tensors: tuple[Tensor, ...]
    wires: tuple[Wire, ...]

    @property
    def scalar_multiplier(self) -> int:
        """Account for variables that occur in no normalized clause."""

        return 1 << len(self.formula.unused_variables)

    @property
    def expected_wire_count(self) -> int:
        return self.formula.literal_count + 2 * sum(
            max(degree - 3, 0) // (self.degree_cap - 2)
            for degree in self.formula.occurrence_degrees
        )

    def validate(self) -> None:
        if len(self.wires) != self.expected_wire_count:
            raise AssertionError("exact wire-count identity failed")
        seen_ports = [0] * len(self.wires)
        for i, tensor in enumerate(self.tensors):
            if tensor.index != i or tensor.side not in (0, 1):
                raise AssertionError("bad tensor index or bipartition label")
            if tensor.kind == "clause":
                if tensor.side != 0 or len(tensor.edges) > 3:
                    raise AssertionError("bad clause-side tensor")
                if len(tensor.edges) != len(tensor.signs):
                    raise AssertionError("literal/port ordering mismatch")
            elif tensor.kind == "equality":
                if not 1 <= len(tensor.edges) <= self.degree_cap:
                    raise AssertionError("equality degree cap failed")
                if tensor.side == 0 and len(tensor.edges) != 2:
                    raise AssertionError("a subdivision must have two ports")
            else:
                raise AssertionError("unknown tensor kind")
            for edge in tensor.edges:
                if not 0 <= edge < len(self.wires):
                    raise AssertionError("bad port index")
                wire = self.wires[edge]
                if i not in (wire.left, wire.right):
                    raise AssertionError("port does not meet its tensor")
                seen_ports[edge] += 1
        if any(count != 2 for count in seen_ports):
            raise AssertionError("each wire must have two ports")
        for wire in self.wires:
            if self.tensors[wire.left].side != 0 or self.tensors[wire.right].side != 1:
                raise AssertionError("network is not bipartite")
            if not 1 <= wire.variable <= self.formula.n_variables:
                raise AssertionError("wire has no valid source variable")

    def weight(self, edge_bits: Sequence[int]) -> int:
        if len(edge_bits) != len(self.wires):
            raise ValueError("one bit is required for every wire")
        for tensor in self.tensors:
            if not tensor.entry(tuple(edge_bits[e] for e in tensor.edges)):
                return 0
        return 1


def build_network(formula: Formula, degree_cap: int = 3) -> Network:
    """Construct the exact path-of-equalities normalization in linear size.

    With d external ports, k equality vertices along a path have capacity
    k(B-2)+2. The minimum k is max(1, ceil((d-2)/(B-2))). Each internal
    path connection is subdivided once to keep all variable-gadget vertices
    on the same side of the bipartition.
    """

    _integer(degree_cap, "degree_cap", 3)
    if normalize_3cnf(formula.n_variables, formula.clauses) != formula:
        raise ValueError("formula must be normalized by normalize_3cnf")
    records: list[dict] = []
    wires: list[Wire] = []

    def add_tensor(kind: str, side: int, signs=(), variable=None) -> int:
        index = len(records)
        records.append(dict(index=index, kind=kind, side=side, edges=[],
                            signs=tuple(signs), variable=variable))
        return index

    def connect(a: int, b: int, variable: int, internal: bool) -> None:
        if records[a]["side"] == 1:
            a, b = b, a
        if records[a]["side"] != 0 or records[b]["side"] != 1:
            raise AssertionError("connection does not cross the bipartition")
        edge = len(wires)
        wires.append(Wire(a, b, variable, internal))
        records[a]["edges"].append(edge)
        records[b]["edges"].append(edge)

    occurrence_nodes: list[list[int]] = [[] for _ in range(formula.n_variables)]
    for clause in formula.clauses:
        node = add_tensor("clause", 0, signs=(literal > 0 for literal in clause))
        for literal in clause:
            occurrence_nodes[abs(literal) - 1].append(node)

    for variable, clause_nodes in enumerate(occurrence_nodes, start=1):
        degree = len(clause_nodes)
        if degree == 0:
            continue
        width = degree_cap - 2
        count = max(1, (degree - 2 + width - 1) // width)
        path = [add_tensor("equality", 1, variable=variable) for _ in range(count)]
        for a, b in zip(path, path[1:]):
            midpoint = add_tensor("equality", 0, variable=variable)
            connect(a, midpoint, variable, True)
            connect(midpoint, b, variable, True)
        cursor = 0
        for i, node in enumerate(path):
            internal_degree = int(i > 0) + int(i + 1 < count)
            capacity = degree_cap - internal_degree
            take = min(capacity, degree - cursor)
            for clause_node in clause_nodes[cursor:cursor + take]:
                connect(clause_node, node, variable, False)
            cursor += take
        if cursor != degree:
            raise AssertionError("equality path has insufficient capacity")

    tensors = tuple(Tensor(**{**record, "edges": tuple(record["edges"])})
                    for record in records)
    network = Network(formula, degree_cap, tensors, tuple(wires))
    network.validate()
    return network


def count_formula_bruteforce(formula: Formula, max_variables: int = 20) -> int:
    """Exhaustive reference counter, for tests only."""

    if formula.n_variables > max_variables:
        raise ValueError("formula exceeds the brute-force verification limit")
    return sum(formula.accepts(bits) for bits in product((0, 1), repeat=formula.n_variables))


def count_network_bruteforce(network: Network, max_wires: int = 20) -> int:
    """Exhaustive integer contraction, multiplied by the unused-variable factor.

    This intentionally exponential reference routine is not the proposed
    asymptotic SAT algorithm or a practical tensor-contraction backend.
    """

    network.validate()
    if len(network.wires) > max_wires:
        raise ValueError("network exceeds the brute-force verification limit")
    return network.scalar_multiplier * sum(
        network.weight(bits) for bits in product((0, 1), repeat=len(network.wires))
    )
