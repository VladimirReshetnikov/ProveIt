"""Exact reference implementation for the accompanying research manuscript.

Standard library only.  This is an effective compiler, not an instantiation
of a small universal counter machine.  Natural inputs exclude bool and float.
Graph equations are checked on support AND all its neighbors.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from typing import Iterable, Mapping


def nat(x: object, name: str = "value") -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return x


def odd_parameter(m: int) -> int:
    if type(m) is not int or m < 3 or m % 2 != 1:
        raise ValueError("m must be odd and at least 3")
    return m


@dataclass(frozen=True)
class Instruction:
    """HALT; INC(counter, target); or TEST(counter, zero_target, positive_target)."""
    op: str
    counter: int = 0
    target: int = 0
    positive: int = 0


@dataclass(frozen=True)
class Branch:
    tag: int
    source: int
    target: int
    counter: int
    kind: str  # inc, zero, positive

    def delta(self, j: int) -> int:
        return (1 if self.kind == "inc" else -1 if self.kind == "positive" else 0) if j == self.counter else 0

    def enabled(self, counters: tuple[int, ...]) -> bool:
        return self.kind == "inc" or (counters[self.counter] == 0 if self.kind == "zero" else counters[self.counter] > 0)


@dataclass(frozen=True)
class Node:
    state: int
    counters: tuple[int, ...]
    history: int


@dataclass(frozen=True)
class Program:
    dimension: int
    instructions: tuple[Instruction, ...]
    start: int = 0

    def __post_init__(self) -> None:
        nat(self.dimension, "dimension")
        if self.dimension < 1 or type(self.instructions) is not tuple or not self.instructions:
            raise ValueError("use a positive dimension and a nonempty immutable instruction tuple")
        nat(self.start, "start")
        if self.start >= len(self.instructions):
            raise ValueError("start state out of range")
        if any(not isinstance(i, Instruction) for i in self.instructions):
            raise ValueError("all program entries must be Instruction records")
        if sum(i.op == "HALT" for i in self.instructions) != 1:
            raise ValueError("exactly one HALT instruction is required")
        for i in self.instructions:
            if not isinstance(i, Instruction) or i.op not in {"HALT", "INC", "TEST"}:
                raise ValueError("invalid instruction")
            for x in (i.counter, i.target, i.positive):
                nat(x, "instruction field")
            if i.counter >= self.dimension:
                raise ValueError("counter index out of range")
            if i.target >= len(self.instructions) or i.positive >= len(self.instructions):
                raise ValueError("target state out of range")

    @property
    def halt(self) -> int:
        return next(q for q, i in enumerate(self.instructions) if i.op == "HALT")

    @property
    def branches(self) -> tuple[Branch, ...]:
        out: list[Branch] = []
        for q, i in enumerate(self.instructions):
            for kind, dest in (("inc", i.target),) if i.op == "INC" else (("zero", i.target), ("positive", i.positive)) if i.op == "TEST" else ():
                out.append(Branch(len(out) + 1, q, dest, i.counter, kind))
        return tuple(out)

    @property
    def base(self) -> int:
        return max(2, len(self.branches) + 1)

    def validate(self, v: Node) -> None:
        if not isinstance(v, Node) or type(v.counters) is not tuple:
            raise ValueError("an immutable Node is required")
        nat(v.state, "state")
        nat(v.history, "history")
        if v.state >= len(self.instructions) or v.history == 0 or len(v.counters) != self.dimension:
            raise ValueError("invalid node")
        for c in v.counters:
            nat(c, "counter")

    def root(self, counters: tuple[int, ...]) -> Node:
        v = Node(self.start, counters, 1)
        self.validate(v)
        return v

    def selected(self, v: Node) -> Branch | None:
        self.validate(v)
        return next((r for r in self.branches if r.source == v.state and r.enabled(v.counters)), None)

    def successor(self, v: Node) -> Node | None:
        r = self.selected(v)
        if r is None:
            return None
        return Node(r.target, tuple(c + r.delta(j) for j, c in enumerate(v.counters)), self.base * v.history + r.tag)

    def predecessor(self, v: Node) -> Node | None:
        self.validate(v)
        h, tag = divmod(v.history, self.base)
        if h == 0 or not 1 <= tag <= len(self.branches):
            return None
        r = self.branches[tag - 1]
        c = tuple(x - r.delta(j) for j, x in enumerate(v.counters))
        if r.target != v.state or min(c) < 0 or not r.enabled(c):
            return None
        p = Node(r.source, c, h)
        return p if self.successor(p) == v else None

    def neighbors(self, v: Node) -> tuple[Node, ...]:
        return tuple(w for w in (self.predecessor(v), self.successor(v)) if w is not None)

    def trace(self, counters: tuple[int, ...], horizon: int) -> tuple[Node, ...]:
        nat(horizon, "horizon")
        out = [self.root(counters)]
        for _ in range(horizon):
            w = self.successor(out[-1])
            if w is None:
                break
            out.append(w)
        return tuple(out)


def pair(a: int, b: int) -> int:
    nat(a); nat(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    nat(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def tuple_code(xs: tuple[int, ...]) -> int:
    if not xs:
        raise ValueError("nonempty tuple required")
    for x in xs:
        nat(x)
    return xs[0] if len(xs) == 1 else pair(xs[0], tuple_code(xs[1:]))


def tuple_decode(n: int, length: int) -> tuple[int, ...]:
    nat(n); nat(length)
    if length == 0:
        raise ValueError("positive tuple length required")
    if length == 1:
        return (n,)
    a, b = unpair(n)
    return (a,) + tuple_decode(b, length - 1)


def encode_node(p: Program, v: Node) -> int:
    p.validate(v)
    return len(p.instructions) * tuple_code(v.counters + (v.history - 1,)) + v.state


def decode_node(p: Program, n: int) -> Node:
    nat(n)
    rest, q = divmod(n, len(p.instructions))
    xs = tuple_decode(rest, p.dimension + 1)
    return Node(q, xs[:-1], xs[-1] + 1)


def connected_neighbors(p: Program, index: int) -> tuple[int, ...]:
    """4n,4n+1: rails; 4n+2: coupling hub; 4n+3: backbone."""
    nat(index, "vertex")
    n, kind = divmod(index, 4)
    if kind <= 1:
        v = decode_node(p, n)
        return tuple(sorted([4 * encode_node(p, w) + kind for w in p.neighbors(v)] + [4 * n + 2]))
    if kind == 2:
        return (4 * n, 4 * n + 1, 4 * n + 3)
    return tuple(sorted([4 * n + 2, 4 * (n + 1) + 3] + ([4 * (n - 1) + 3] if n else [])))


def swap(index: int) -> int:
    nat(index)
    return index ^ 1 if index % 4 <= 1 else index


def apply_operator(p: Program, values: Mapping[int, int | Fraction], m: int = 5) -> dict[int, int | Fraction]:
    """Exact A_m on a finite-support array, including every exterior row."""
    odd_parameter(m)
    if m < 5:
        raise ValueError("connected network requires m >= 5")
    out: dict[int, int | Fraction] = {}
    for v, a in values.items():
        nat(v, "vertex")
        if type(a) is not int and not isinstance(a, Fraction):
            raise ValueError("only exact integer or Fraction coefficients are accepted")
        if a:
            out[v] = out.get(v, 0) + m * a
            for w in connected_neighbors(p, v):
                out[w] = out.get(w, 0) - a
    return {v: a for v, a in out.items() if a}


def lucas_u(m: int, n: int) -> int:
    odd_parameter(m); nat(n, "index")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, m * b - a
    return a


def continuant(m: int, j: int) -> int:
    nat(j, "continuant index")
    return lucas_u(m, j + 1)


def canonical_network_certificate(p: Program, counters: tuple[int, ...], horizon: int, m: int = 5) -> tuple[int, dict[int, int]]:
    odd_parameter(m)
    if m < 5:
        raise ValueError("connected network requires m >= 5")
    tr = p.trace(counters, horizon)
    if tr[-1].state != p.halt:
        raise ValueError("no halting certificate within the supplied horizon")
    length = len(tr)
    vals: dict[int, int] = {}
    for i, v in enumerate(tr):
        k = 4 * encode_node(p, v)
        z = continuant(m, length - i - 1)
        vals[k], vals[k + 1] = z, -z
    return continuant(m, length), vals


def is_prime(p: int) -> bool:
    return type(p) is int and p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def valuation(n: int, p: int) -> int:
    if type(n) is not int or n == 0 or not is_prime(p):
        raise ValueError("valuation requires nonzero integer and prime")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def rank_of_apparition(m: int, p: int) -> int:
    odd_parameter(m)
    if not is_prime(p):
        raise ValueError("prime required")
    a, b = 0, 1
    for n in range(1, p * p):
        a, b = b, (m * b - a) % p
        if a == 0:
            return n
    raise AssertionError("invertible recurrence did not return to a scalar power")


def localization_bound(m: int, primes: Iterable[int]) -> dict:
    """All S-smooth D_L have L < first_excluded_length (a sufficient bound)."""
    odd_parameter(m)
    ps = tuple(sorted(set(primes)))
    if any(not is_prime(p) for p in ps):
        raise ValueError("S must contain only primes")
    C = 1
    ranks = []
    for p in ps:
        z = rank_of_apparition(m, p)
        v = valuation(lucas_u(m, z), p)
        c = max(0, v - valuation(z, p))
        C *= p ** c
        ranks.append({"prime": p, "rank": z, "valuation_at_rank": v, "c": c})
    L = 1
    while (m - 1) ** L <= C * (L + 1):
        L += 1
    return {"m": m, "primes": list(ps), "C": C, "first_excluded_length": L, "ranks": ranks}


def smooth(n: int, primes: Iterable[int]) -> bool:
    nat(n)
    if n == 0:
        raise ValueError("smoothness requires a positive integer")
    ps = tuple(set(primes))
    if any(not is_prime(p) for p in ps):
        raise ValueError("prime set required")
    for p in ps:
        while n % p == 0:
            n //= p
    return n == 1


def localized_membership(p: Program, counters: tuple[int, ...], primes: Iterable[int], m: int = 5) -> bool:
    if m < 5:
        raise ValueError("connected network requires m >= 5")
    info = localization_bound(m, primes)
    B = info["first_excluded_length"]
    if B <= 1:
        p.root(counters)  # still validate input
        return False
    tr = p.trace(counters, B - 2)
    return tr[-1].state == p.halt and smooth(continuant(m, len(tr)), info["primes"])


# Quadratic polynomial compiler.  Linear forms use key '' for the constant.
Linear = dict[str, int]
Monomial = tuple[str, ...]


def linear(*terms: tuple[int, str], constant: int = 0) -> Linear:
    out: Linear = {"": constant} if constant else {}
    for coefficient, variable in terms:
        out[variable] = out.get(variable, 0) + coefficient
    return {x: a for x, a in out.items() if a}


def eval_linear(row: Linear, assignment: Mapping[str, int]) -> int:
    return sum(a * (assignment[x] if x else 1) for x, a in row.items())


@dataclass(frozen=True)
class Certificate:
    variables: tuple[str, ...]
    parameters: tuple[str, ...]
    rows: tuple[Linear, ...]
    cross_terms: tuple[tuple[str, str], ...]

    def _validate_assignment(self, assignment: Mapping[str, int]) -> None:
        for name in self.variables + self.parameters:
            if name not in assignment or type(assignment[name]) is not int:
                raise ValueError(f"missing or nonintegral coordinate: {name}")

    def energy(self, assignment: Mapping[str, int], natural: bool = True) -> int:
        self._validate_assignment(assignment)
        if natural and any(assignment[x] < 0 for x in self.variables + self.parameters):
            raise ValueError("the zero-set theorem is over natural coordinates")
        return sum(eval_linear(r, assignment) ** 2 for r in self.rows) + sum(assignment[a] * assignment[b] for a, b in self.cross_terms)

    def expanded(self) -> dict[Monomial, int]:
        out: dict[Monomial, int] = {}
        for row in self.rows:
            for x, a in row.items():
                for y, b in row.items():
                    mon = tuple(sorted(v for v in (x, y) if v))
                    out[mon] = out.get(mon, 0) + a * b
        for x, y in self.cross_terms:
            mon = tuple(sorted((x, y)))
            out[mon] = out.get(mon, 0) + 1
        return {mon: c for mon, c in out.items() if c}

    def export(self) -> dict:
        return {"domain": "natural numbers", "variables": self.variables, "parameters": self.parameters,
                "linear_residuals": self.rows, "nonnegative_cross_terms": self.cross_terms,
                "expanded_polynomial": [{"coefficient": c, "variables": mon} for mon, c in sorted(self.expanded().items())],
                "total_degree": max(map(len, self.expanded()), default=0)}


def compile_certificate(p: Program, T: int, m: int = 5) -> Certificate:
    nat(T, "horizon"); odd_parameter(m)
    branches = p.branches
    d = p.dimension
    vars_: list[str] = []
    rows: list[Linear] = []
    cross: list[tuple[str, str]] = []
    for t in range(T + 1):
        vars_.extend([f"q{t}", f"h{t}"] + [f"c{t}_{j}" for j in range(d)])
    for t in range(T):
        for r in branches:
            vars_.append(f"b{t}_{r.tag}")
            vars_.extend(f"a{t}_{r.tag}_{j}" for j in range(d))
            if r.kind == "positive":
                vars_.append(f"s{t}_{r.tag}")
    vars_.extend([f"u{i}" for i in range(T + 1)] + ["charge"])
    params = tuple(f"x{j}" for j in range(d))
    rows.extend([linear((1, "q0"), constant=-p.start), linear((1, "h0"), constant=-1)])
    rows.extend(linear((1, f"c0_{j}"), (-1, f"x{j}")) for j in range(d))
    rows.append(linear((1, f"q{T}"), constant=-p.halt))
    for t in range(T):
        rows.append(linear(*[(1, f"b{t}_{r.tag}") for r in branches], constant=-1))
        rows.append(linear((1, f"q{t}"), *[(-r.source, f"b{t}_{r.tag}") for r in branches]))
        rows.append(linear((1, f"q{t+1}"), *[(-r.target, f"b{t}_{r.tag}") for r in branches]))
        for j in range(d):
            rows.append(linear((1, f"c{t}_{j}"), *[(-1, f"a{t}_{r.tag}_{j}") for r in branches]))
            rows.append(linear((1, f"c{t+1}_{j}"), (-1, f"c{t}_{j}"), *[(-r.delta(j), f"b{t}_{r.tag}") for r in branches]))
        rows.append(linear((1, f"h{t+1}"), (-p.base, f"h{t}"), *[(-r.tag, f"b{t}_{r.tag}") for r in branches]))
        for r in branches:
            if r.kind == "zero":
                rows.append(linear((1, f"a{t}_{r.tag}_{r.counter}")))
            elif r.kind == "positive":
                rows.append(linear((1, f"a{t}_{r.tag}_{r.counter}"), (-1, f"b{t}_{r.tag}"), (-1, f"s{t}_{r.tag}")))
            for s in branches:
                if r != s:
                    cross.extend((f"b{t}_{s.tag}", f"a{t}_{r.tag}_{j}") for j in range(d))
    for i in range(T + 1):
        terms = [(m, f"u{i}")]
        if i: terms.append((-1, f"u{i-1}"))
        if i < T: terms.append((-1, f"u{i+1}"))
        if i == 0: terms.append((-1, "charge"))
        rows.append(linear(*terms))
    rows.append(linear((1, f"u{T}"), constant=-1))
    return Certificate(tuple(vars_), params, tuple(rows), tuple(cross))


def canonical_assignment(p: Program, counters: tuple[int, ...], T: int, m: int = 5) -> dict[str, int]:
    cert = compile_certificate(p, T, m)
    tr = p.trace(counters, T)
    if len(tr) != T + 1 or tr[-1].state != p.halt:
        raise ValueError("T must be the exact first halting time")
    out = dict.fromkeys(cert.variables, 0)
    out.update({f"x{j}": c for j, c in enumerate(counters)})
    for t, v in enumerate(tr):
        out[f"q{t}"], out[f"h{t}"] = v.state, v.history
        out.update({f"c{t}_{j}": c for j, c in enumerate(v.counters)})
        if t < T:
            r = p.selected(v)
            if r is None:
                raise AssertionError("unexpected early halt")
            out[f"b{t}_{r.tag}"] = 1
            out.update({f"a{t}_{r.tag}_{j}": c for j, c in enumerate(v.counters)})
            if r.kind == "positive":
                out[f"s{t}_{r.tag}"] = v.counters[r.counter] - 1
    out.update({f"u{i}": continuant(m, T - i) for i in range(T + 1)})
    out["charge"] = continuant(m, T + 1)
    return out


def countdown() -> Program:
    return Program(1, (Instruction("TEST", 0, 1, 0), Instruction("HALT")))


def divergent() -> Program:
    return Program(1, (Instruction("INC", 0, 0), Instruction("HALT")))


def transfer() -> Program:
    return Program(2, (Instruction("TEST", 0, 2, 1), Instruction("INC", 1, 0), Instruction("HALT")))
