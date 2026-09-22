#!/usr/bin/env python3
"""Finite exact checks for the accompanying computable-surreal article.

Python 3.10+; standard library only. Exponents and coefficients are Fractions.
This checks finite identities and finite test fixtures. It is NOT a surreal
implementation, a real-oracle implementation, a proof checker, or a halting
oracle. No finite run proves the article's undecidability or closure theorems.
"""
from __future__ import annotations

import argparse
import json
import math
import random
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from typing import Iterable, Mapping

Series = dict[Q, Q]


def clean(items: Mapping[Q, Q]) -> Series:
    """Canonicalize a finite exact series; exact rational zero tests are safe."""
    return {Q(q): Q(a) for q, a in items.items() if a != 0}


def add(x: Series, y: Series) -> Series:
    z = dict(x)
    for q, a in y.items():
        z[q] = z.get(q, Q(0)) + a
    return clean(z)


def scale(x: Series, a: Q) -> Series:
    return clean({q: a * c for q, c in x.items()})


def sub(x: Series, y: Series) -> Series:
    return add(x, scale(y, Q(-1)))


def mul(x: Series, y: Series, cutoff: Q | None = None) -> Series:
    """Full finite convolution, optionally retaining only exponents < cutoff."""
    z: Series = {}
    for r, a in x.items():
        for s, b in y.items():
            q = r + s
            if cutoff is None or q < cutoff:
                z[q] = z.get(q, Q(0)) + a * b
    return clean(z)


def power(x: Series, n: int, cutoff: Q | None = None) -> Series:
    if n < 0:
        raise ValueError("power requires a nonnegative integer")
    if cutoff is not None and any(q < 0 for q in x):
        raise ValueError("intermediate truncation requires nonnegative support")
    result: Series = {Q(0): Q(1)}
    for _ in range(n):
        result = mul(result, x, cutoff)
    return result


def truncate(x: Series, cutoff: Q) -> Series:
    return {q: a for q, a in x.items() if q < cutoff}


def unit_inverse(x: Series, n: int) -> Series:
    """The article's unit inverse recurrence on the integer grid, modulo t**n."""
    if n < 1:
        raise ValueError("n must be positive")
    if any(q < 0 or q.denominator != 1 for q in x):
        raise ValueError("unit_inverse expects a nonnegative integer grid")
    a0 = x.get(Q(0), Q(0))
    if a0 == 0:
        raise ZeroDivisionError("a nonzero constant coefficient is required")
    b: list[Q] = [1 / a0]
    for k in range(1, n):
        b.append(-sum((x.get(Q(j), Q(0)) * b[k-j]
                       for j in range(1, k+1)), Q(0)) / a0)
    return clean({Q(k): a for k, a in enumerate(b)})


def derivative(x: Series) -> Series:
    return clean({q - 1: q * a for q, a in x.items()})


def primitive_without_residue(x: Series) -> Series:
    return clean({q + 1: a / (q + 1)
                  for q, a in x.items() if q != -1})


def compose(coefficients: Iterable[Q], h: Series, cutoff: Q) -> Series:
    if any(q <= 0 for q in h):
        raise ValueError("composition requires strictly positive support")
    z: Series = {}
    hpower: Series = {Q(0): Q(1)}
    for c in coefficients:
        z = add(z, scale(hpower, c))
        hpower = mul(hpower, h, cutoff)
    return truncate(z, cutoff)


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def equal(self, group: str, actual: object, expected: object) -> None:
        if actual != expected:
            raise AssertionError(f"{group}: {actual!r} != {expected!r}")
        self.counts[group] += 1

    def true(self, group: str, condition: bool) -> None:
        self.equal(group, condition, True)


def first_halt_at(fixture: Mapping[int, int], e: int, s: int) -> bool:
    """Finite fixture ONLY, not the real predicate for arbitrary machines."""
    return fixture.get(e) == s


def support_coefficient(q: Q, fixture: Mapping[int, int], side: str) -> Q:
    """The rational-query arithmetic from the decidable-support construction."""
    if side not in {"A", "B"}:
        raise ValueError("side must be A or B")
    if q <= 0:
        return Q(0)
    e = 0
    while True:
        c = Q(4 ** (e + 1))
        if side == "A":
            if c > q:
                return Q(0)
            delta = q - c
        else:
            if 2 * c - Q(1, 2) > q:
                return Q(0)
            delta = 2 * c - q
        if 0 < delta <= Q(1, 2):
            stage = 1 / delta - 2
            if stage.denominator == 1 and stage >= 0:
                return Q(int(first_halt_at(fixture, e, int(stage))))
            return Q(0)
        e += 1


def finite_cover(x: Series, lower: Q, bound: Q,
                 extras: Iterable[Q] = ()) -> set[Q]:
    """A complete finite cover, allowing arbitrary zero candidates."""
    if any(q < lower for q in x):
        raise ValueError("invalid lower bound")
    return {q for q in set(x) | set(extras) if lower <= q < bound}


def run_checks(seed: int = 20260921) -> dict[str, object]:
    rng = random.Random(seed)
    checks = Checks()
    one: Series = {Q(0): Q(1)}
    t: Series = {Q(1): Q(1)}

    # Finite convolution and candidate covers, including zero candidates.
    for _ in range(100):
        x = clean({Q(rng.randint(-8, 12), 3): Q(rng.randint(-5, 5), 3)
                   for _ in range(7)})
        y = clean({Q(rng.randint(-6, 14), 2): Q(rng.randint(-4, 4), 5)
                   for _ in range(7)})
        lx = min(x, default=Q(0)) - 1
        ly = min(y, default=Q(0)) - 1
        product = mul(x, y)
        extras = {Q(k, 6) for k in range(-20, 31, 5)}
        bound = Q(rng.randint(-8, 16), 2)
        fx = finite_cover(x, lx, bound - ly, extras)
        fy = finite_cover(y, ly, bound - lx, extras)
        candidate = {r+s for r in fx for s in fy
                     if lx+ly <= r+s < bound}
        checks.true("product_cover", set(truncate(product, bound)) <= candidate)
        queries = set(product) | {Q(k, 6) for k in range(-20, 30, 7)}
        for q in queries:
            cover = finite_cover(x, lx, q-ly+1, extras)
            value = sum((x.get(r, Q(0))*y.get(q-r, Q(0)) for r in cover), Q(0))
            checks.equal("finite_coefficient_formula", value, product.get(q, Q(0)))
        checks.equal("commutative_product", mul(x, y), mul(y, x))
        checks.equal("Leibniz", derivative(product),
                     add(mul(derivative(x), y), mul(x, derivative(y))))
        residue = x.get(Q(-1), Q(0))
        checks.equal("primitive_residue_identity", derivative(primitive_without_residue(x)),
                     sub(x, clean({Q(-1): residue})))

    # Exact, untruncated finite geometric remainders on fractional grids.
    for n in range(9):
        h = {Q(1, 3): Q(2), Q(5, 3): Q(-1, 2)}
        partial: Series = {}
        for j in range(n+1):
            partial = add(partial, power(h, j))
        checks.equal("geometric_remainder", mul(sub(one, h), partial),
                     sub(one, power(h, n+1)))

    # Unit inversion for varying exact coefficients and truncation lengths.
    for n in range(1, 30):
        x = clean({Q(0): Q(3, 2), Q(1): Q(-2), Q(3): Q(7, 5), Q(8): Q(-1)})
        checks.equal("unit_inverse", mul(x, unit_inverse(x, n), Q(n)), one)

    # Newton/Hensel for Y**2 = 1+t, maintaining the claimed doubling bound.
    hensel_trace: list[dict[str, object]] = []
    n = 32
    target = add(one, t)
    y = dict(one)
    for step in range(6):
        error = sub(mul(y, y, Q(n)), target)
        error = truncate(error, Q(n))
        checks.true("Hensel_doubling", not error or min(error) >= 2**step)
        hensel_trace.append({"iteration": step,
                             "error_order": str(min(error)) if error else f">={n}"})
        if error:
            correction = mul(error, unit_inverse(scale(y, Q(2)), n), Q(n))
            y = sub(y, correction)
    checks.equal("Hensel_root_identity", mul(y, y, Q(n)), target)
    binom = [Q(1)]
    for j in range(1, n):
        binom.append(binom[-1] * (Q(1, 2)-(j-1)) / j)
    checks.equal("binomial_square_root", y, clean({Q(j): a for j, a in enumerate(binom)}))

    # Formal identities modulo t**n, not real convergence claims.
    for n in range(2, 20):
        exp_coeff = [Q(1, math.factorial(j)) for j in range(n)]
        exp_t = {Q(j): a for j, a in enumerate(exp_coeff)}
        exp_neg = {Q(j): a * (-1)**j for j, a in enumerate(exp_coeff)}
        log_coeff = [Q(0)] + [Q((-1)**(j+1), j) for j in range(1, n)]
        log_one_t = compose(log_coeff, t, Q(n))
        checks.equal("exp_inverse", mul(exp_t, exp_neg, Q(n)), one)
        checks.equal("exp_log", compose(exp_coeff, log_one_t, Q(n)), add(one, t))
        checks.equal("log_exp", compose(log_coeff, sub(exp_t, one), Q(n)), t)

    # Finite fixtures for the halting-product collision identity.
    for trial in range(25):
        fixture = {e: rng.randint(0, 100) for e in range(10) if rng.randrange(2)}
        A = {Q(4**(e+1)) + Q(1, s+2): Q(1) for e, s in fixture.items()}
        B = {Q(2*4**(e+1)) - Q(1, s+2): Q(1) for e, s in fixture.items()}
        AB = mul(A, B)
        for e in range(12):
            checks.equal("halting_fixture_product", AB.get(Q(3*4**(e+1)), Q(0)),
                         Q(int(e in fixture)))
        for side, series in (("A", A), ("B", B)):
            queries = set(series) | {q + Q(1, 7) for q in series}
            queries |= {Q(-1), Q(0), Q(4), Q(8), Q(12), Q(5, 2)}
            for q in queries:
                checks.equal("support_query_fixture", support_coefficient(q, fixture, side),
                             series.get(q, Q(0)))

    # The inverse reduction's two exact algebraic cases at exponent -1.
    for a in (Q(0), Q(1), Q(1, 8), Q(1, 1024)):
        inverse = {Q(-1): Q(1)} if a == 0 else unit_inverse({Q(0): a, Q(1): Q(1)}, 8)
        checks.equal("inverse_obstruction_fixture", inverse.get(Q(-1), Q(0)), Q(int(a == 0)))

    # Increasing, left-finite exponents with unbounded reduced denominators.
    exponents = [Q(j) + Q(1, j+1) for j in range(1, 100)]
    checks.true("unbounded_denominator_fixture", all(a < b for a, b in zip(exponents, exponents[1:])))
    for j, q in enumerate(exponents, start=1):
        checks.equal("unbounded_denominator_fixture", q.denominator, j+1)

    return {
        "status": "PASS",
        "seed": seed,
        "total_checks": sum(checks.counts.values()),
        "groups": dict(sorted(checks.counts.items())),
        "Hensel_trace_mod_t_32": hensel_trace,
        "scope": "Finite exact-rational checks only; not formal verification or a halting oracle.",
        "repository_revision_reviewed": "4896a2808ce30e01b1c86ae3ba2295a64762d246",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON report path")
    args = parser.parse_args()
    report = run_checks()
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
