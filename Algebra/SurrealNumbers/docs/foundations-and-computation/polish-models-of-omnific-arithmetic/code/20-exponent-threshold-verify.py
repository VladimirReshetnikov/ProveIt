#!/usr/bin/env python3
"""Exact finite diagnostics for the exponent-group threshold manuscript.

Python 3.10+; standard library only. These checks are NOT a formal proof of
any statement about Polish spaces, Borel sets, infinite series, or probability.
They exercise finite algebra and the integer inequalities used in the proofs.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
import sys
from typing import Iterable

SEED = 20261004
COUNTS: dict[str, int] = {}


def check(condition: bool, group: str, detail: object = "") -> None:
    """Do not use Python assert: checks must also run under python -O."""
    COUNTS[group] = COUNTS.get(group, 0) + 1
    if not condition:
        raise AssertionError(f"{group}: {detail}")


@dataclass(frozen=True)
class Poly:
    """Finite generalized Laurent polynomial with exact rational data."""
    terms: tuple[tuple[F, F], ...]  # sorted by exponent, no zero coefficients

    @staticmethod
    def make(terms: Iterable[tuple[int | F, int | F]]) -> Poly:
        acc: dict[F, F] = {}
        for exponent, coefficient in terms:
            exponent, coefficient = F(exponent), F(coefficient)
            acc[exponent] = acc.get(exponent, F(0)) + coefficient
        return Poly(tuple(sorted((e, c) for e, c in acc.items() if c)))

    @staticmethod
    def const(n: int | F) -> Poly:
        return Poly.make([(0, n)])

    @staticmethod
    def monomial(e: int | F, c: int | F = 1) -> Poly:
        return Poly.make([(e, c)])

    def __add__(self, other: Poly) -> Poly:
        return Poly.make((*self.terms, *other.terms))

    def __neg__(self) -> Poly:
        return Poly.make((e, -c) for e, c in self.terms)

    def __sub__(self, other: Poly) -> Poly:
        return self + (-other)

    def __mul__(self, other: Poly) -> Poly:
        return Poly.make((e + f, c * d)
                         for e, c in self.terms for f, d in other.terms)

    def __pow__(self, n: int) -> Poly:
        if not isinstance(n, int) or n < 0:
            raise ValueError("Only nonnegative integer powers are supported")
        result, base = Poly.const(1), self
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n //= 2
        return result

    @property
    def degree(self) -> F | None:
        return self.terms[-1][0] if self.terms else None

    @property
    def leading(self) -> F:
        return self.terms[-1][1] if self.terms else F(0)

    @property
    def sign(self) -> int:
        return (self.leading > 0) - (self.leading < 0)

    @property
    def constant(self) -> F:
        return next((c for e, c in self.terms if e == 0), F(0))

    @property
    def is_integer_part_ring(self) -> bool:
        return all(e >= 0 for e, _ in self.terms) and self.constant.denominator == 1

    def le(self, other: Poly) -> bool:
        return (other - self).sign >= 0

    def lt(self, other: Poly) -> bool:
        return (other - self).sign > 0


ZERO, ONE = Poly.const(0), Poly.const(1)


def floor_fraction(x: F) -> int:
    return x.numerator // x.denominator


def division(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    """Full order division on rational-exponent, rational-coefficient examples.

    Long division terminates because each finite input has a common rational
    exponent denominator. The final constant is corrected if the remaining
    infinitesimal tail is negative at an integral constant.
    """
    if not a.is_integer_part_ring or not b.is_integer_part_ring:
        raise ValueError("Inputs must have nonnegative exponents and integral constants")
    if a.sign < 0 or b.sign <= 0:
        raise ValueError("Require a >= 0, b > 0")
    q, rem = ZERO, a
    steps = 0
    while rem.terms and rem.degree >= b.degree:  # type: ignore[operator]
        term = Poly.monomial(rem.degree - b.degree, rem.leading / b.leading)  # type: ignore[operator]
        q = q + term
        rem = rem - term * b
        steps += 1
        if steps > 10000:
            raise RuntimeError("Diagnostic long-division step limit exceeded")
    c = q.constant
    z = floor_fraction(c)
    if c.denominator == 1 and rem.sign < 0:
        z -= 1
    q = q - Poly.const(c) + Poly.const(z)
    return q, a - b * q


def iroot(a: int, k: int) -> int:
    if a < 0 or k < 2:
        raise ValueError("Require a >= 0 and k >= 2")
    if a < 2:
        return a
    lo, hi = 0, 1 << ((a.bit_length() + k - 1) // k)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** k <= a:
            lo = mid
        else:
            hi = mid
    return hi if hi ** k <= a else lo


def exact_rational_root(a: F, k: int) -> F:
    n, d = iroot(a.numerator, k), iroot(a.denominator, k)
    if n ** k != a.numerator or d ** k != a.denominator:
        raise ValueError("The diagnostic requires a rational leading kth root")
    return F(n, d)


def integer_poly_root(a: Poly, k: int) -> Poly:
    """Binomial principal-part construction for finite rational examples.

    Negative series tails are not numerically approximated. A final exact
    polynomial comparison detects the negative-infinitesimal correction.
    """
    if not a.is_integer_part_ring or a.sign < 0:
        raise ValueError("Require a nonnegative integer-part-ring element")
    if not a.terms:
        return ZERO
    if a.degree == 0:
        return Poly.const(iroot(int(a.constant), k))
    degree = a.degree
    root_degree = degree / k  # type: ignore[operator]
    root_coefficient = exact_rational_root(a.leading, k)
    epsilon = a * Poly.monomial(-degree, 1 / a.leading) - ONE  # type: ignore[operator]
    leading_root = Poly.monomial(root_degree, root_coefficient)
    principal = leading_root
    if epsilon.terms:
        eta = -epsilon.degree  # type: ignore[operator]
        bound = floor_fraction(root_degree / eta)
        power = ONE
        coefficient = F(1)
        for n in range(1, bound + 1):
            power = power * epsilon
            coefficient *= (F(1, k) - (n - 1)) / n
            term = leading_root * power * Poly.const(coefficient)
            principal = principal + Poly.make((e, c) for e, c in term.terms if e >= 0)
    c = principal.constant
    q = principal - Poly.const(c) + Poly.const(floor_fraction(c))
    if not (q ** k).le(a):
        q = q - ONE
    return q


def random_positive(rng: random.Random, denominator: int = 4) -> Poly:
    d = rng.randint(0, 12)
    if d == 0:
        return Poly.const(rng.randint(0, 15))
    indices = rng.sample(range(1, d), k=min(rng.randint(0, 3), d - 1))
    terms: list[tuple[int | F, int | F]] = [(0, rng.randint(-8, 8))]
    terms.extend((F(j, denominator), F(rng.randint(-5, 5), rng.randint(1, 4)))
                 for j in indices)
    terms.append((F(d, denominator), F(rng.randint(1, 5), rng.randint(1, 4))))
    return Poly.make(terms)


def run() -> dict[str, object]:
    rng = random.Random(SEED)
    # Signs, degrees and integral constant terms of positive semiring operations.
    for _ in range(600):
        a, b, c = (random_positive(rng, rng.choice([1, 2, 4])) for _ in range(3))
        check((a + b).sign >= 0 and (a * b).sign >= 0, "semiring positivity")
        check((a + b).is_integer_part_ring and (a * b).is_integer_part_ring,
              "integer constant closure")
        check(a * (b + c) == a * b + a * c, "distributivity")
        if a.terms and b.terms:
            check((a + b).degree == max(a.degree, b.degree), "addition degree")
            check((a * b).degree == a.degree + b.degree, "product degree")
        if b.sign > 0:
            q, r = division(a, b)
            check(q.is_integer_part_ring and r.is_integer_part_ring, "division membership")
            check(a == b * q + r and q.sign >= 0 and r.sign >= 0 and r.lt(b),
                  "full division bounds", (a, b, q, r))

    t = Poly.monomial(1)
    for a, b, expected in [
        (t*t - ONE, t, t - ONE),
        (t*t + ONE, t, t),
        (t*t - t, t, t - ONE),
        (Poly.const(7), Poly.const(3), Poly.const(2)),
    ]:
        q, r = division(a, b)
        check(q == expected and ZERO.le(r) and r.lt(b), "floor-tail edge cases")

    # Generalized-polynomial integer roots. Leading coefficients are chosen
    # to have exact rational roots; no floating-point approximation is used.
    for k in [2, 3, 4]:
        for _ in range(70):
            a = random_positive(rng, 4)
            if a.degree is not None and a.degree > 0:
                top = a.degree
                a = a - Poly.monomial(top, a.leading)
                a = a + Poly.monomial(top, rng.randint(1, 3) ** k)
            q = integer_poly_root(a, k)
            check(q.is_integer_part_ring and q.sign >= 0, "root membership")
            check((q ** k).le(a) and a.lt((q + ONE) ** k), "root interval", (k, a, q))
    # Infinitesimal-tail boundary in the binomial expansion.
    check(integer_poly_root(t*t - ONE, 2) == t - ONE, "root-tail edge cases")
    check(integer_poly_root(t*t + ONE, 2) == t, "root-tail edge cases")

    # Integer root and quotient inequalities used to manufacture grids.
    for k in [2, 3, 4, 5]:
        samples = [rng.getrandbits(bits) + 10000 for bits in [16, 32, 64, 128, 256]
                   for _ in range(12)]
        for c in samples:
            r = c
            for _ in range(8):
                s = iroot(r, k)
                nxt = iroot(s, k)
                check(nxt ** (k*k) <= r < (nxt + 1) ** (k*k), "double-root interval")
                if nxt <= 3:
                    break
                a, anext = c // r, c // nxt
                check(a >= 1 and a*nxt <= c, "root-grid boundedness")
                check(anext > 5*a*nxt, "root-grid separation", (k, c, r, nxt, a, anext))
                r = nxt

    # Every finite signed perturbation is controlled by its last nonzero bit.
    y = [6 ** i for i in range(8)]
    for coefficients in product([-1, 0, 1], repeat=8):
        indices = [i for i, d in enumerate(coefficients) if d]
        if not indices:
            continue
        j = indices[-1]
        value = 2 * sum(d * v for d, v in zip(coefficients, y))
        check(abs(value) > y[j], "finite-flip separation")
    for n in range(6):
        for k in range(1, 10):
            values = sorted(2*sum(bit*6**j for bit, j in zip(bits, range(n+1, n+k+1)))
                            for bits in product([0, 1], repeat=k))
            check(all(b-a > 6**n for a, b in zip(values, values[1:])),
                  "finite-block anti-concentration")

    # Metric-budget estimates, independent of a hypothetical topology.
    for _ in range(20):
        ds = [F(1)] + [F(rng.randint(1, 100), 100) for _ in range(39)]
        deltas = [F(1, 2**(n+3))*min(ds[:n+1]) for n in range(len(ds))]
        for n in range(1, len(ds)):
            check(sum(deltas[n:]) <= ds[n]*F(1, 2**(n+2)), "fusion budget")

    # Exact exponents for a countable bounded dense-group grid model.
    C = Poly.monomial(1)
    for n in range(24):
        alpha = 1 - F(1, 2**(n+1))
        beta = F(1, 2**(n+3))
        alpha_next = 1 - F(1, 2**(n+2))
        a, u = Poly.monomial(alpha), Poly.monomial(beta)
        anext = Poly.monomial(alpha_next)
        check((a*u).lt(C) and (Poly.const(5)*a*u).lt(anext), "dyadic exponent grids")
        i = Poly.monomial(beta/2, F(1, 3))
        j = Poly.monomial(beta/2, F(7, 5))
        check(ZERO.le(i) and i.lt(j) and j.lt(u), "grid index examples")
        difference = a*(j-i)
        check(a.le(difference) and difference.le(a*u), "grid difference examples")

    return {
        "status": "PASS",
        "seed": SEED,
        "python": sys.version.split()[0],
        "arithmetic": "integers and fractions.Fraction only",
        "assertions_by_group": COUNTS,
        "total_assertions": sum(COUNTS.values()),
        "scope": "Finite algebraic diagnostics; not a formal verification of the infinite theorems",
    }


def main() -> None:
    try:
        result = run()
    except Exception as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        raise
    output = Path(__file__).resolve().parent / "verification_results.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
