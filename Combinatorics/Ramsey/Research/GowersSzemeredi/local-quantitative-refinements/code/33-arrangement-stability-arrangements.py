#!/usr/bin/env python3
"""Exact cyclic-group arrangement counting and nearest-model decoding.

Only Python's standard library is required.  All probabilities are Fractions.
An s-test uses s vertical differences, hence 2*s point occurrences; s is even.
The model is a(x) + b*x*y + c*y modulo q, NOT necessarily a biaffine map.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, comb, isqrt
import json
from pathlib import Path
from typing import Sequence

Table = Sequence[Sequence[int]]


def validate(table: Table, q: int) -> tuple[int, int]:
    if type(q) is not int or q < 1:
        raise ValueError("The target modulus q must be a positive integer.")
    if not table or not table[0]:
        raise ValueError("The table must have at least one row and one column.")
    n, m = len(table), len(table[0])
    if any(len(row) != m for row in table):
        raise ValueError("The table must be rectangular.")
    if any(type(v) is not int or not 0 <= v < q for row in table for v in row):
        raise ValueError("Every table entry must be an integer in range(q).")
    return n, m


def validate_order(s: int) -> None:
    if type(s) is not int or s < 4 or s % 2:
        raise ValueError("s must be an even integer at least 4.")


@dataclass(frozen=True)
class Model:
    n: int
    m: int
    q: int
    b: int
    c: int
    a: tuple[int, ...]
    mismatches: int

    def value(self, x: int, y: int) -> int:
        return (self.a[x] + (self.b * x + self.c) * y) % self.q

    @property
    def distance(self) -> Fraction:
        return Fraction(self.mismatches, self.n * self.m)

    def as_dict(self) -> dict:
        return {"n": self.n, "m": self.m, "q": self.q,
                "b": self.b, "c": self.c, "a": list(self.a),
                "mismatches": self.mismatches,
                "distance": str(self.distance)}


def decode(table: Table, q: int) -> Model:
    """Return an exact nearest vertical-arrangement model, with stable tie breaking."""
    n, m = validate(table, q)
    gb, gc = gcd(gcd(n, m), q), gcd(m, q)
    best: Model | None = None
    for ib in range(gb):
        b = ib * (q // gb)
        for ic in range(gc):
            c = ic * (q // gc)
            offsets: list[int] = []
            matches = 0
            for x, row in enumerate(table):
                counts = Counter((v - (b * x + c) * y) % q
                                 for y, v in enumerate(row))
                top = max(counts.values())
                offsets.append(min(t for t, k in counts.items() if k == top))
                matches += top
            candidate = Model(n, m, q, b, c, tuple(offsets), n * m - matches)
            if best is None or candidate.mismatches < best.mismatches:
                best = candidate
    assert best is not None
    return best


def verify_model(table: Table, q: int, model: Model) -> bool:
    """Check feasibility and claimed score, not optimality."""
    n, m = validate(table, q)
    if (model.n, model.m, model.q) != (n, m, q) or len(model.a) != n:
        return False
    if not (0 <= model.b < q and 0 <= model.c < q):
        return False
    if (n * model.b) % q or (m * model.b) % q or (m * model.c) % q:
        return False
    if any(type(v) is not int or not 0 <= v < q for v in model.a):
        return False
    actual = sum(table[x][y] != model.value(x, y)
                 for x in range(n) for y in range(m))
    return actual == model.mismatches


def convolution(a: list[int], b: list[int], n: int, q: int) -> list[int]:
    """Unnormalized convolution of integer arrays on Z_n x Z_q."""
    result = [0] * (n * q)
    aa = [(i // q, i % q, v) for i, v in enumerate(a) if v]
    bb = [(i // q, i % q, v) for i, v in enumerate(b) if v]
    for x, z, av in aa:
        for y, w, bv in bb:
            result[((x + y) % n) * q + (z + w) % q] += av * bv
    return result


def convolution_power(a: list[int], exponent: int, n: int, q: int) -> list[int]:
    result = [0] * (n * q)
    result[0] = 1
    power = a
    while exponent:
        if exponent & 1:
            result = convolution(result, power, n, q)
        exponent >>= 1
        if exponent:
            power = convolution(power, power, n, q)
    return result


def count(table: Table, q: int, s: int = 4) -> tuple[int, int]:
    """Return (respected, total), counting ordered arrangements and repetitions."""
    n, m = validate(table, q)
    validate_order(s)
    respected = 0
    for h in range(m):
        multiplicity = [0] * (n * q)
        for x, row in enumerate(table):
            for y in range(m):
                z = (row[(y + h) % m] - row[y]) % q
                multiplicity[x * q + z] += 1
        sums = convolution_power(multiplicity, s // 2, n, q)
        respected += sum(v * v for v in sums)
    total = n ** (s - 1) * m ** (s + 1)
    assert 0 <= respected <= total
    return respected, total


def count_partial(table: Sequence[Sequence[int | None]], q: int,
                  s: int = 4) -> tuple[int, int, int]:
    """Return (respected, valid, full_total), with None denoting an erasure.

    Conditional failure is undefined when valid is zero.
    """
    filled = [[0 if v is None else v for v in row] for row in table]
    n, m = validate(filled, q)
    validate_order(s)
    respected = valid = 0
    for h in range(m):
        multiplicity = [0] * (n*q)
        row_sizes = [0] * n
        for x, row in enumerate(table):
            for y in range(m):
                before, after = row[y], row[(y+h) % m]
                if before is not None and after is not None:
                    row_sizes[x] += 1
                    multiplicity[x*q+(after-before) % q] += 1
        sums = convolution_power(multiplicity, s//2, n, q)
        row_sums = convolution_power(row_sizes, s//2, n, 1)
        respected += sum(v*v for v in sums)
        valid += sum(v*v for v in row_sums)
    total = n**(s-1)*m**(s+1)
    assert 0 <= respected <= valid <= total
    return respected, valid, total


def error(table: Table, q: int, s: int = 4) -> Fraction:
    respected, total = count(table, q, s)
    return Fraction(total - respected, total)


def defect_lower(delta: Fraction, s: int) -> Fraction:
    validate_order(s)
    return s * delta * (1 - 2 * delta) * (
        (1 - 2 * delta) ** (s - 2) - (2 * delta) ** (s - 2))


def quadratic_lower(delta: Fraction, s: int) -> Fraction:
    validate_order(s)
    return s * delta - 2 * s * (s - 1) * delta * delta


def sharp_family_error(n: int, s: int) -> Fraction:
    if type(n) is not int or n < 3 or n % 2 != 1:
        raise ValueError("The sharp family requires odd n >= 3.")
    validate_order(s)
    u = Fraction(2, n)
    return (1 - (1 - u) ** s - (n - 1) * u ** s) / 4


def prime_family_error(p: int, s: int) -> Fraction:
    """Exact row-defect error on Z_p x Z_p -> Z_p, for odd prime p."""
    if type(p) is not int or p < 3 or any(p % d == 0 for d in range(2, isqrt(p)+1)):
        raise ValueError("p must be an odd prime.")
    validate_order(s)
    rho, half = Fraction(1, p), s // 2
    iid_rejection = Fraction(0)
    signed_rejection = 0
    for a in range(half+1):
        for b in range(half+1):
            if (a-b) % p:
                multiplicity = comb(half, a)*comb(half, b)
                iid_rejection += multiplicity*rho**(a+b)*(1-rho)**(s-a-b)
                signed_rejection += multiplicity*(-1)**(a+b)
    return (1-rho)*(iid_rejection+signed_rejection*(rho**(s-1)-rho**s))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help='JSON with keys "q" and "table"')
    parser.add_argument("--orders", nargs="+", type=int, default=[4, 16])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        table, q = data["table"], data["q"]
        model = decode(table, q)
        result = {"model": model.as_dict(), "arrangements": []}
        for s in args.orders:
            good, total = count(table, q, s)
            result["arrangements"].append({"s": s, "gowers_arrangement_order": s // 2,
                "respected": good, "total": total, "error": str(Fraction(total-good, total))})
    except (OSError, KeyError, TypeError, ValueError) as exc:
        parser.exit(2, f"error: {exc}\n")
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
