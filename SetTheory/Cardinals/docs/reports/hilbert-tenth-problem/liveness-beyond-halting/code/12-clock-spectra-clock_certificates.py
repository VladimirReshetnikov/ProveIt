"""Exact natural-number quadratic certificates for labelled two-stack traces.

Python 3.10+, standard library only. This is a finite certificate compiler,
not a solver for infinite paths, a halting oracle, or a formal proof checker.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Iterable, Mapping, Sequence
import json

Monomial = tuple[str, ...]

class Poly:
    """Sparse polynomial with arbitrary-precision integer coefficients."""
    def __init__(self, terms: Mapping[Monomial, int] | None = None):
        self.terms: dict[Monomial, int] = {}
        for mon, coeff in (terms or {}).items():
            if not isinstance(coeff, int):
                raise TypeError("Coefficients must be integers")
            key = tuple(sorted(mon))
            self.terms[key] = self.terms.get(key, 0) + coeff
        self.terms = {m: c for m, c in self.terms.items() if c}

    @staticmethod
    def coerce(value: Poly | int) -> Poly:
        if isinstance(value, Poly):
            return value
        if isinstance(value, int):
            return Poly({(): value})
        raise TypeError("Expected polynomial or integer")

    @staticmethod
    def var(name: str) -> Poly:
        return Poly({(name,): 1})

    def __add__(self, other: Poly | int) -> Poly:
        result = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            result[m] = result.get(m, 0) + c
        return Poly(result)
    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: Poly | int) -> Poly:
        result: dict[Monomial, int] = {}
        for a, c in self.terms.items():
            for b, d in self.coerce(other).terms.items():
                key = tuple(sorted(a + b))
                result[key] = result.get(key, 0) + c*d
        return Poly(result)
    __rmul__ = __mul__

    def square(self) -> Poly:
        return self*self

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Mapping[str, int]) -> int:
        total = 0
        for mon, coeff in self.terms.items():
            v = coeff
            for name in mon:
                v *= values[name]
            total += v
        return total

    def serialized(self) -> list[dict]:
        return [{"monomial": list(m), "coefficient": c}
                for m, c in sorted(self.terms.items(), key=lambda x: (len(x[0]), x[0]))]

OPS = {"stay", "empty", "push0", "push1", "pop0", "pop1"}

@dataclass(frozen=True)
class Rule:
    source: int
    target: int
    left: str = "stay"
    right: str = "stay"

    def __post_init__(self) -> None:
        if type(self.source) is not int or type(self.target) is not int:
            raise TypeError("States must be integers")
        if min(self.source, self.target) < 0:
            raise ValueError("States must be natural numbers")
        if self.left not in OPS or self.right not in OPS:
            raise ValueError("Unrecognized stack operation")

@dataclass(frozen=True)
class Machine:
    rules: tuple[Rule, ...]
    initial: tuple[int, int, int]
    accepting: frozenset[int]

    def __post_init__(self) -> None:
        if len(self.initial) != 3 or any(type(x) is not int or x < 0 for x in self.initial):
            raise ValueError("Initial configuration must be three natural numbers")
        if any(type(x) is not int or x < 0 for x in self.accepting):
            raise ValueError("Accepting states must be natural numbers")


def stack_residual(op: str, old: Poly | int, new: Poly | int) -> Poly | int:
    if op == "stay": return new-old
    if op == "empty": return old+new
    if op.startswith("push"): return new-2*old-int(op[-1])-1
    if op.startswith("pop"): return old-2*new-int(op[-1])-1
    raise ValueError("Unrecognized stack operation")


def guarded_affine(D: Poly, s: Poly, a: Poly, b: Poly) -> Poly:
    if D.degree > 1:
        raise ValueError("The guarded residual must be affine")
    return (D-a+b).square() + a*b + s*(a+b)


def decode_stack(u: int) -> tuple[int, ...]:
    """Bottom-to-top bits; u+1 has a leading sentinel bit 1."""
    if type(u) is not int or u < 0:
        raise ValueError("Stack code must be a natural number")
    return tuple(int(c) for c in bin(u+1)[3:])


def encode_stack(bits: Sequence[int]) -> int:
    x = 1
    for bit in bits:
        if bit not in (0, 1): raise ValueError("Nonbinary stack entry")
        x = 2*x + bit
    return x-1


def literal_stack_step(bits: tuple[int, ...], op: str) -> tuple[int, ...] | None:
    """Independent list semantics: no affine residuals are used."""
    if op == "stay": return bits
    if op == "empty": return () if not bits else None
    bit = int(op[-1])
    if op.startswith("push"): return bits+(bit,)
    if op.startswith("pop"): return bits[:-1] if bits and bits[-1] == bit else None
    raise ValueError("Unrecognized operation")


def literal_step(config: tuple[int, int, int], rule: Rule) -> tuple[int, int, int] | None:
    state, left, right = config
    if state != rule.source: return None
    l = literal_stack_step(decode_stack(left), rule.left)
    r = literal_stack_step(decode_stack(right), rule.right)
    if l is None or r is None: return None
    return rule.target, encode_stack(l), encode_stack(r)

@dataclass
class Certificate:
    machine: Machine
    horizon: int
    deadlines: tuple[int, ...]
    polynomial: Poly
    variables: tuple[str, ...]

    def validate(self, assignment: Mapping[str, int]) -> bool:
        if set(assignment) != set(self.variables):
            return False
        if any(type(v) is not int or v < 0 for v in assignment.values()):
            return False
        return self.polynomial.evaluate(assignment) == 0

    def canonical(self, labels: Sequence[int]) -> dict[str, int]:
        if len(labels) != self.horizon:
            raise ValueError("Wrong trace length")
        values: dict[str, int] = {}
        configs = [self.machine.initial]
        ticks = [0]
        for r in labels:
            if type(r) is not int or not 0 <= r < len(self.machine.rules):
                raise ValueError("Invalid rule index")
            nxt = literal_step(configs[-1], self.machine.rules[r])
            if nxt is None: raise ValueError("Illegal labelled trace")
            configs.append(nxt)
            ticks.append(ticks[-1] + int(nxt[0] in self.machine.accepting))
        for t, config in enumerate(configs):
            for name, value in zip(("q", "u", "v"), config):
                values[f"{name}_{t}"] = value
        for t in range(self.horizon):
            old, new = configs[t], configs[t+1]
            for r, rule in enumerate(self.machine.rules):
                values[f"s_{t}_{r}"] = int(labels[t] == r)
                ds = (old[0]-rule.source, new[0]-rule.target,
                      stack_residual(rule.left, old[1], new[1]),
                      stack_residual(rule.right, old[2], new[2]))
                for j, d in enumerate(ds):
                    assert isinstance(d, int)
                    values[f"a_{t}_{r}_{j}"] = max(d, 0)
                    values[f"b_{t}_{r}_{j}"] = max(-d, 0)
        for i, deadline in enumerate(self.deadlines, start=1):
            z = ticks[deadline]-i
            if z < 0: raise ValueError("A deadline is missed")
            values[f"z_{i}"] = z
        if not self.validate(values):
            raise AssertionError("Compiler/canonical-lift disagreement")
        return values

    def export(self, path: str, assignment: Mapping[str, int] | None = None) -> None:
        data = {"domain": "nonnegative integers", "horizon": self.horizon,
                "deadlines": self.deadlines, "degree": self.polynomial.degree,
                "variables": self.variables, "variable_count": len(self.variables),
                "monomial_count": len(self.polynomial.terms),
                "terms": self.polynomial.serialized(),
                "machine": {"initial": self.machine.initial,
                            "accepting": sorted(self.machine.accepting),
                            "rules": [r.__dict__ for r in self.machine.rules]}}
        if assignment is not None:
            data["zero_assignment"] = dict(assignment)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
            f.write("\n")


def compile_certificate(machine: Machine, horizon: int,
                        deadlines: Sequence[int] = ()) -> Certificate:
    if type(horizon) is not int or horizon < 0:
        raise ValueError("Horizon must be a natural number")
    if any(type(d) is not int or not 0 <= d <= horizon for d in deadlines):
        raise ValueError("Every deadline must lie in the external horizon")
    names: list[str] = []
    def v(name: str) -> Poly:
        names.append(name)
        return Poly.var(name)
    configs = [(v(f"q_{t}"), v(f"u_{t}"), v(f"v_{t}"))
               for t in range(horizon+1)]
    selectors = [[v(f"s_{t}_{r}") for r in range(len(machine.rules))]
                 for t in range(horizon)]
    p = sum(((x-c).square() for x,c in zip(configs[0], machine.initial)), Poly())
    for t in range(horizon):
        p += (sum(selectors[t], Poly())-1).square()
        old, new = configs[t], configs[t+1]
        for r, rule in enumerate(machine.rules):
            residuals = (old[0]-rule.source, new[0]-rule.target,
                         stack_residual(rule.left, old[1], new[1]),
                         stack_residual(rule.right, old[2], new[2]))
            for j, d in enumerate(residuals):
                assert isinstance(d, Poly)
                p += guarded_affine(d, selectors[t][r],
                                    v(f"a_{t}_{r}_{j}"), v(f"b_{t}_{r}_{j}"))
    for i, deadline in enumerate(deadlines, start=1):
        tick_count = sum((selectors[t][r] for t in range(deadline)
                          for r,rule in enumerate(machine.rules)
                          if rule.target in machine.accepting), Poly())
        p += (tick_count-i-v(f"z_{i}")).square()
    expected = 3*(horizon+1)+9*len(machine.rules)*horizon+len(deadlines)
    assert len(names) == len(set(names)) == expected
    assert p.degree <= 2
    return Certificate(machine, horizon, tuple(deadlines), p, tuple(names))


def example_machine() -> Machine:
    """Nonuniversal seven-rule test fixture; arbitrary bit transfer with ticks."""
    return Machine((Rule(0,0,"push0"), Rule(0,0,"push1"), Rule(0,1),
                    Rule(1,1,"pop0","push0"), Rule(1,1,"pop1","push1"),
                    Rule(1,2,"empty"), Rule(2,0)), (0,0,0), frozenset({2}))


def first_match_tree(node: Sequence[int], approximation: Callable[[int,int],int]) -> bool:
    """Recursive singleton-tree predicate from the first-matching-stage theorem.

    approximation(stage, bit) must be a total computable binary function.
    Convergence is an external promise, never decided by this function.
    The input coordinate node[n-1] is a candidate stage for prefix length n.
    """
    words: list[tuple[int, ...]] = []
    for n, stage in enumerate(node, start=1):
        if type(stage) is not int or stage < n: return False
        word = tuple(approximation(stage, j) for j in range(n))
        if any(bit not in (0,1) for bit in word):
            raise ValueError("The approximation must be binary")
        if words and word[:-1] != words[-1]: return False
        for earlier in range(n, stage):
            if tuple(approximation(earlier,j) for j in range(n)) == word:
                return False
        words.append(word)
    return True


def first_matches(length: int, approximation: Callable[[int,int],int],
                  limit: Callable[[int],int]) -> tuple[int, ...]:
    """Compute a finite true path prefix using the limit as a supplied oracle."""
    answer = []
    for n in range(1, length+1):
        target = tuple(limit(j) for j in range(n))
        stage = n
        while tuple(approximation(stage,j) for j in range(n)) != target:
            stage += 1
        answer.append(stage)
    return tuple(answer)
