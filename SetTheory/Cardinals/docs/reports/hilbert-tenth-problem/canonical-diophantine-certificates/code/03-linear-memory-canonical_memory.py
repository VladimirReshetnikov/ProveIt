#!/usr/bin/env python3
"""Canonical natural-number Diophantine certificates for finite RAM access logs.

Coefficients are integers; all parameters and witnesses range over N, including 0.
The output polynomial is the sum of squares of the emitted quadratic residuals.
No third-party dependencies. This is executable evidence, not a formal proof.
"""
from __future__ import annotations
from dataclasses import dataclass
import argparse
import json
from pathlib import Path
from typing import Iterable

Monomial = tuple[int, ...]

class Poly:
    """Small exact sparse polynomial, with sorted variable-id monomials."""
    def __init__(self, terms: dict[Monomial, int] | None = None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def coerce(value: int | Poly) -> Poly:
        if isinstance(value, Poly):
            return value
        if isinstance(value, int):
            return Poly({(): value})
        raise TypeError(f"Expected int or Poly, got {type(value).__name__}")

    def __add__(self, other: int | Poly) -> Poly:
        result = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            result[m] = result.get(m, 0) + c
        return Poly(result)
    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: int | Poly) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: int | Poly) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: int | Poly) -> Poly:
        result: dict[Monomial, int] = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                key = tuple(sorted(m + n))
                result[key] = result.get(key, 0) + c * d
        return Poly(result)
    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: list[int]) -> int:
        total = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for index in monomial:
                term *= values[index]
            total += term
        return total

    def json_terms(self, names: list[str]) -> list[dict]:
        return [dict(coefficient=c, monomial=[names[i] for i in m])
                for m, c in sorted(self.terms.items(), key=lambda item: (len(item[0]), item[0]))]

@dataclass(frozen=True)
class Event:
    address: int
    write: int
    value: int

    def __post_init__(self):
        for x in (self.address, self.write, self.value):
            if not isinstance(x, int) or x < 0:
                raise ValueError("Event coordinates must be nonnegative integers")

class System:
    def __init__(self):
        self.names: list[str] = []
        self.values: list[int] = []
        self.roles: list[str] = []
        self.residuals: list[Poly] = []
        self.labels: list[str] = []
        self.comparators = 0
        self.padded_length = 0
        self.sorted_records: list[tuple[Poly, ...]] = []

    def variable(self, name: str, value: int, role: str = "witness") -> Poly:
        if value < 0:
            raise ValueError(f"Negative canonical value for {name}")
        i = len(self.names)
        self.names.append(name)
        self.values.append(value)
        self.roles.append(role)
        return Poly({(i,): 1})

    def eq(self, label: str, residual: int | Poly):
        p = Poly.coerce(residual)
        if p.degree > 2:
            raise ValueError(f"Nonquadratic residual: {label}")
        self.labels.append(label)
        self.residuals.append(p)

    def value(self, p: int | Poly) -> int:
        return Poly.coerce(p).evaluate(self.values)

    def violations(self, values: list[int] | None = None) -> list[str]:
        xs = self.values if values is None else values
        if len(xs) != len(self.names):
            raise ValueError("Incorrect assignment length")
        if any(not isinstance(x, int) or x < 0 for x in xs):
            return ["natural-number domain"]
        return [label for label, p in zip(self.labels, self.residuals)
                if p.evaluate(xs) != 0]

    def energy(self, values: list[int] | None = None) -> int:
        xs = self.values if values is None else values
        return sum(p.evaluate(xs) ** 2 for p in self.residuals)

    def expanded_polynomial(self) -> Poly:
        result = Poly()
        for p in self.residuals:
            result = result + p * p
        return result

    def summary(self) -> dict:
        return dict(parameters=self.roles.count("parameter"),
                    witnesses=self.roles.count("witness"),
                    residuals=len(self.residuals), comparators=self.comparators,
                    padded_length=self.padded_length,
                    maximum_residual_degree=max((p.degree for p in self.residuals), default=0),
                    polynomial_degree_bound=4,
                    maximum_witness_bits=max((v.bit_length() for v, r in zip(self.values, self.roles)
                                              if r == "witness"), default=0),
                    energy=self.energy(), violations=self.violations())

    def export(self, destination: Path, expanded: bool = False):
        destination.mkdir(parents=True, exist_ok=True)
        data = dict(domain="N including zero; integer coefficients", summary=self.summary(),
                    variables=[dict(name=n, role=r, canonical_value=str(v))
                               for n, r, v in zip(self.names, self.roles, self.values)],
                    polynomial="sum of squares of the following residuals",
                    residuals=[dict(label=l, terms=p.json_terms(self.names))
                               for l, p in zip(self.labels, self.residuals)])
        (destination / "certificate.json").write_text(json.dumps(data, indent=2) + "\n")
        if expanded:
            p = self.expanded_polynomial()
            (destination / "polynomial.json").write_text(json.dumps(
                dict(degree=p.degree, terms=p.json_terms(self.names)), indent=2) + "\n")


def bitonic_network(n: int) -> Iterable[tuple[int, int, bool]]:
    """Yield (left wire, right wire, ascending); n must be a power of two."""
    if n < 1 or n & (n - 1):
        raise ValueError("Network width must be a positive power of two")
    block = 2
    while block <= n:
        stride = block // 2
        while stride:
            for i in range(n):
                j = i ^ stride
                if j > i:
                    yield i, j, (i & block) == 0
            stride //= 2
        block *= 2


def compare_records(s: System, x: tuple[Poly, ...], y: tuple[Poly, ...],
                    ascending: bool) -> tuple[tuple[Poly, ...], tuple[Poly, ...]]:
    """Four fields are (shifted address, chronological key, write flag, value)."""
    cid = s.comparators
    s.comparators += 1
    prefix = f"cmp{cid}"
    a, bkey = x[1], y[1]
    av, bv = s.value(a), s.value(bkey)
    take = int(av <= bv)
    b = s.variable(prefix + ".b", take)
    d = s.variable(prefix + ".d", bv - av if take else av - bv - 1)
    for suffix, residual in [
        ("boolean", b * (b - 1)),
        ("signed_gap", bkey - a - (2 * b - 1) * d - b + 1),
    ]:
        s.eq(prefix + "." + suffix, residual)
    lo, hi = [], []
    for i, (xf, yf) in enumerate(zip(x, y)):
        low = s.variable(f"{prefix}.lo{i}", s.value(xf if take else yf))
        high = s.variable(f"{prefix}.hi{i}", s.value(yf if take else xf))
        s.eq(f"{prefix}.lo{i}", low - b * xf - (1 - b) * yf)
        s.eq(f"{prefix}.hi{i}", high - xf - yf + low)
        lo.append(low)
        hi.append(high)
    return (tuple(lo), tuple(hi)) if ascending else (tuple(hi), tuple(lo))


def valid_log(events: list[Event]) -> bool:
    memory: dict[int, int] = {}
    for event in events:
        if event.write not in (0, 1):
            return False
        if event.write:
            memory[event.address] = event.value
        elif event.value != memory.get(event.address, 0):
            return False
    return True


def compile_log(events: list[Event]) -> System:
    """Compile symbolic event coordinates and produce their canonical assignment.

    Invalid reads are not repaired: their assignment violates the final residuals.
    The graph of all routing/auxiliary computations remains uniquely determined.
    """
    length = len(events)
    n = 1 << (max(1, length) - 1).bit_length()
    s = System()
    s.padded_length = n
    params = []
    for t, event in enumerate(events):
        params.append(tuple(s.variable(f"event{t}.{name}", value, "parameter")
                            for name, value in zip(("a", "w", "v"),
                                                   (event.address, event.write, event.value))))
    records = []
    for t, (a, w, v) in enumerate(params):
        alpha = s.variable(f"event{t}.shifted_address", events[t].address + 1)
        key = s.variable(f"event{t}.key", (n + 1) * (events[t].address + 1) + t)
        s.eq(f"event{t}.address", alpha - a - 1)
        s.eq(f"event{t}.key", key - (n + 1) * alpha - t)
        s.eq(f"event{t}.write_bit", w * (w - 1))
        records.append((alpha, key, w, v))
    for t in range(length, n):
        records.append(tuple(map(Poly.coerce, (0, t, 1, 0))))
    for i, j, ascending in bitonic_network(n):
        records[i], records[j] = compare_records(s, records[i], records[j], ascending)
    s.sorted_records = records
    s.eq("memory.first", (1 - records[0][2]) * records[0][3])
    for j in range(1, n):
        prev, current = records[j - 1], records[j]
        delta = current[0] - prev[0]
        gap = s.value(delta)
        if gap < 0:
            raise AssertionError("Sorting failed to order addresses")
        same = s.variable(f"memory{j}.same", int(gap == 0))
        h = s.variable(f"memory{j}.gap_minus_one", max(0, gap - 1))
        u = s.variable(f"memory{j}.previous_value", s.value(prev[3]) if gap == 0 else 0)
        for suffix, residual in [
            ("boolean", same * (same - 1)),
            ("signed_gap", delta + (2 * same - 1) * h + same - 1),
            ("previous", u - same * prev[3]),
            ("read", (1 - current[2]) * (current[3] - u)),
        ]:
            s.eq(f"memory{j}.{suffix}", residual)
    return s


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON list of [address, write, value] triples")
    parser.add_argument("output", type=Path, help="directory for emitted certificate")
    parser.add_argument("--expanded", action="store_true", help="also expand the quartic polynomial")
    args = parser.parse_args()
    try:
        payload = json.loads(args.input.read_text())
        events = [Event(*row) for row in payload]
        system = compile_log(events)
        system.export(args.output, args.expanded)
        print(json.dumps(system.summary(), indent=2))
    except (ValueError, TypeError, OSError) as exc:
        parser.exit(2, f"Error: {exc}\n")

if __name__ == "__main__":
    main()
