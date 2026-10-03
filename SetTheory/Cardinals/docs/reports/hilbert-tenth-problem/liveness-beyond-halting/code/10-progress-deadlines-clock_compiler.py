"""Exact, dependency-free quartic certificates for finite two-stack traces.

All variables range over nonnegative integers. Polynomials have integer
coefficients. The exported quartic is represented as a sum of squares of
quadratic residuals; no floating-point arithmetic or symbolic black box is used.
This is a finite-horizon compiler, not an implementation of MRDP extraction.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable, Mapping, Sequence
import json

Monomial = tuple[tuple[str, int], ...]


class Poly:
    """Small sparse integer polynomial, suitable for checking local equations."""

    def __init__(self, terms: Mapping[Monomial, int] | None = None):
        self.terms = {m: int(c) for m, c in (terms or {}).items() if c}

    @staticmethod
    def const(value: int) -> Poly:
        return Poly({(): value})

    @staticmethod
    def var(name: str) -> Poly:
        return Poly({((name, 1),): 1})

    @staticmethod
    def coerce(value: Poly | int) -> Poly:
        return value if isinstance(value, Poly) else Poly.const(value)

    def __add__(self, other: Poly | int) -> Poly:
        terms = self.terms.copy()
        for m, c in self.coerce(other).terms.items():
            terms[m] = terms.get(m, 0) + c
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: Poly | int) -> Poly:
        terms: dict[Monomial, int] = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                powers = dict(m)
                for v, p in n:
                    powers[v] = powers.get(v, 0) + p
                mn = tuple(sorted(powers.items()))
                terms[mn] = terms.get(mn, 0) + c * d
        return Poly(terms)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max((sum(p for _, p in m) for m in self.terms), default=0)

    def evaluate(self, values: Mapping[str, int]) -> int:
        result = 0
        for m, c in self.terms.items():
            term = c
            for v, p in m:
                term *= values[v] ** p
            result += term
        return result

    def text(self) -> str:
        if not self.terms:
            return "0"
        out = []
        for m, c in sorted(self.terms.items()):
            factors = "*".join(v if p == 1 else f"{v}^{p}" for v, p in m)
            out.append(str(c) if not factors else f"{c}*{factors}")
        return " + ".join(out).replace("+ -", "- ")

    def to_json(self) -> list[dict]:
        return [{"coefficient": c, "powers": dict(m)}
                for m, c in sorted(self.terms.items())]


# Words are top-first. Natural codes have a leading sentinel 1 in base four.
def encode_stack(word: Sequence[int]) -> int:
    n = 1
    for d in reversed(word):
        if d not in (1, 3):
            raise ValueError("stack digits must be 1 or 3")
        n = 4 * n + d
    return n


def decode_stack(n: int) -> tuple[int, ...]:
    if not isinstance(n, int) or n < 1:
        raise ValueError("invalid stack code")
    word = []
    while n != 1:
        n, d = divmod(n, 4)
        if n < 1 or d not in (1, 3):
            raise ValueError("invalid sentinel/digit in stack code")
        word.append(d)
    return tuple(word)


def rational_stack(word: Sequence[int]) -> Fraction:
    if any(d not in (1, 3) for d in word):
        raise ValueError("stack digits must be 1 or 3")
    return sum((Fraction(d, 4 ** (i + 1)) for i, d in enumerate(word)), Fraction())


@dataclass(frozen=True)
class StackOp:
    # guard: any, empty, top1, top3. update: stay, push1, push3, pop.
    guard: str = "any"
    update: str = "stay"

    def __post_init__(self) -> None:
        if self.guard not in ("any", "empty", "top1", "top3"):
            raise ValueError("unknown stack guard")
        if self.update not in ("stay", "push1", "push3", "pop"):
            raise ValueError("unknown stack update")
        if self.update == "pop" and not self.guard.startswith("top"):
            raise ValueError("pop requires an explicit top guard")

    @property
    def top_digit(self) -> int | None:
        return int(self.guard[-1]) if self.guard.startswith("top") else None

    def apply(self, n: int) -> int | None:
        # Only valid initial/reachable codes are passed by the interpreter.
        if self.guard == "empty" and n != 1:
            return None
        d = self.top_digit
        if d is not None and (n < 4 + d or n % 4 != d):
            return None
        if self.update == "stay":
            return n
        if self.update.startswith("push"):
            return 4 * n + int(self.update[-1])
        return n // 4


@dataclass(frozen=True)
class Rule:
    source: int
    target: int
    left: StackOp = StackOp()
    right: StackOp = StackOp()
    name: str = ""


Config = tuple[int, int, int]


@dataclass(frozen=True)
class Machine:
    rules: tuple[Rule, ...]
    initial: Config
    accepting: frozenset[int]

    def __post_init__(self) -> None:
        if any(r.source < 0 or r.target < 0 for r in self.rules):
            raise ValueError("control labels must be natural numbers")
        if self.initial[0] < 0 or any(q < 0 for q in self.accepting):
            raise ValueError("control labels must be natural numbers")
        decode_stack(self.initial[1])
        decode_stack(self.initial[2])

    @property
    def G(self) -> int:
        return sum(op.top_digit is not None for r in self.rules
                   for op in (r.left, r.right))

    @property
    def E(self) -> int:
        return sum(op.guard == "empty" for r in self.rules
                   for op in (r.left, r.right))

    def step(self, c: Config, rule_id: int) -> Config | None:
        r = self.rules[rule_id]
        if c[0] != r.source:
            return None
        x, y = r.left.apply(c[1]), r.right.apply(c[2])
        if x is None or y is None:
            return None
        return r.target, x, y

    def run(self, ids: Sequence[int]) -> list[Config] | None:
        states = [self.initial]
        for r in ids:
            nxt = self.step(states[-1], r)
            if nxt is None:
                return None
            states.append(nxt)
        return states


@dataclass
class Certificate:
    machine: Machine
    horizon: int
    deadlines: tuple[int, ...]
    variables: tuple[str, ...]
    residuals: tuple[tuple[str, Poly], ...]

    def residual_values(self, values: Mapping[str, int]) -> list[int]:
        if set(values) != set(self.variables):
            raise ValueError("assignment has missing or extra variables")
        if any(not isinstance(v, int) or isinstance(v, bool) or v < 0
               for v in values.values()):
            raise ValueError("all witnesses must be nonnegative integers")
        return [p.evaluate(values) for _, p in self.residuals]

    def evaluate(self, values: Mapping[str, int]) -> int:
        return sum(v * v for v in self.residual_values(values))

    def expanded_polynomial(self) -> Poly:
        return sum((p * p for _, p in self.residuals), Poly.const(0))

    def witness(self, ids: Sequence[int]) -> dict[str, int] | None:
        if len(ids) != self.horizon:
            raise ValueError("rule sequence does not match the horizon")
        trace = self.machine.run(ids)
        if trace is None:
            return None
        a = {v: 0 for v in self.variables}
        for t, rid in enumerate(ids):
            for label, value in zip(("q", "x", "y"), trace[t + 1]):
                a[f"{label}_{t+1}"] = value
            a[f"e_{t}_{rid}"] = 1
            r = self.machine.rules[rid]
            for label, op, old in (("x", r.left, trace[t][1]),
                                   ("y", r.right, trace[t][2])):
                if op.top_digit is not None:
                    a[f"u_{t}_{rid}_{label}"] = old // 4 - 1
        for j, h in enumerate(self.deadlines, 1):
            count = sum(trace[t][0] in self.machine.accepting
                        for t in range(1, h + 1))
            if count < j:
                return None
            a[f"w_{j}"] = count - j
        return a

    def export(self) -> dict:
        return {
            "domain": "all variables are nonnegative integers",
            "quartic": "sum of squares of all listed residuals",
            "horizon": self.horizon,
            "deadlines": list(self.deadlines),
            "variables": list(self.variables),
            "residuals": [{"label": name, "text": p.text(), "terms": p.to_json()}
                          for name, p in self.residuals],
        }


def compile_trace(machine: Machine, horizon: int,
                  deadlines: Sequence[int] = ()) -> Certificate:
    if not isinstance(horizon, int) or horizon < 0:
        raise ValueError("horizon must be nonnegative")
    ds = tuple(deadlines)
    if any(not isinstance(d, int) or d < 1 or d > horizon for d in ds):
        raise ValueError("deadlines must be positive and at most the horizon")
    if any(a >= b for a, b in zip(ds, ds[1:])):
        raise ValueError("deadlines must be strictly increasing")
    names: list[str] = []
    residuals: list[tuple[str, Poly]] = []

    def var(name: str) -> Poly:
        if name not in names:
            names.append(name)
        return Poly.var(name)

    def cfg(label: str, t: int) -> Poly:
        if t == 0:
            return Poly.const(machine.initial[("q", "x", "y").index(label)])
        return var(f"{label}_{t}")

    def add(label: str, p: Poly) -> None:
        residuals.append((label, p))

    for t in range(horizon):
        q, x, y = (cfg(label, t) for label in ("q", "x", "y"))
        qn, xn, yn = (cfg(label, t + 1) for label in ("q", "x", "y"))
        indicators = [var(f"e_{t}_{r}") for r in range(len(machine.rules))]
        for rid, e in enumerate(indicators):
            add(f"boolean[{t},{rid}]", e * (e - 1))
        add(f"onehot[{t}]", sum(indicators, Poly.const(0)) - 1)
        for rid, r in enumerate(machine.rules):
            e = indicators[rid]
            add(f"source[{t},{rid}]", e * (q - r.source))
            for label, old, new, op in (("x", x, xn, r.left),
                                         ("y", y, yn, r.right)):
                u = None
                if op.guard == "empty":
                    add(f"empty[{t},{rid},{label}]", e * (old - 1))
                if op.top_digit is not None:
                    u = var(f"u_{t}_{rid}_{label}")
                    add(f"top[{t},{rid},{label}]",
                        e * (old - 4 * u - 4 - op.top_digit))
                    add(f"inactive[{t},{rid},{label}]", (1 - e) * u)
                if op.update == "stay":
                    update = new - old
                elif op.update.startswith("push"):
                    update = new - 4 * old - int(op.update[-1])
                else:
                    assert u is not None
                    update = new - u - 1
                add(f"update[{t},{rid},{label}]", e * update)
        add(f"target[{t}]", qn - sum((r.target * e for r, e in
                                      zip(machine.rules, indicators)), Poly.const(0)))
    for j, h in enumerate(ds, 1):
        count = sum((Poly.var(f"e_{t}_{rid}")
                     for t in range(h) for rid, r in enumerate(machine.rules)
                     if r.target in machine.accepting), Poly.const(0))
        add(f"deadline[{j}]", count - j - var(f"w_{j}"))
    result = Certificate(machine, horizon, ds, tuple(names), tuple(residuals))
    R, G, E, k = len(machine.rules), machine.G, machine.E, len(ds)
    assert len(names) == horizon * (3 + R + G) + k
    assert len(residuals) == horizon * (4 * R + E + 2 * G + 2) + k
    assert all(p.degree <= 2 for _, p in residuals)
    return result


def example_machine() -> Machine:
    """Choose 1 or 3, push it, then pop it and emit one accepting visit."""
    return Machine((
        Rule(0, 1, StackOp("any", "push1"), name="choose1"),
        Rule(0, 1, StackOp("any", "push3"), name="choose3"),
        Rule(1, 2, StackOp("top1", "pop"), name="pop1"),
        Rule(1, 2, StackOp("top3", "pop"), name="pop3"),
        Rule(2, 0, StackOp("empty", "stay"), name="restart"),
    ), (0, 1, 1), frozenset({2}))


if __name__ == "__main__":
    from pathlib import Path
    root = Path(__file__).resolve().parents[1] / "artifacts"
    root.mkdir(exist_ok=True)
    cert = compile_trace(example_machine(), 5, (2, 5))
    ids = (0, 2, 4, 1, 3)
    assignment = cert.witness(ids)
    assert assignment is not None and cert.evaluate(assignment) == 0
    data = cert.export()
    data.update({"rule_sequence": list(ids), "witness": assignment,
                 "variable_count": len(cert.variables),
                 "residual_count": len(cert.residuals),
                 "expanded_degree": cert.expanded_polynomial().degree})
    (root / "example_certificate.json").write_text(json.dumps(data, indent=2) + "\n")
    print(f"Wrote exact certificate: {len(cert.variables)} variables, "
          f"{len(cert.residuals)} residuals, Q(witness)={cert.evaluate(assignment)}")
