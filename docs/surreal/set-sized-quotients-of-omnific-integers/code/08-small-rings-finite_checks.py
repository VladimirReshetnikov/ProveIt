#!/usr/bin/env python3
"""Exact finite checks accompanying 'What Small Rings Can See of Omnific Integers'.

Run with Python 3.10 or later. Only the standard library is used.
These are finite sanity checks, not a formal verification of infinite Hahn sums,
real closedness, cardinal arguments, or the theorems about proper classes.
"""
from __future__ import annotations

from fractions import Fraction as Q
from random import Random
from collections import Counter
from typing import TypeAlias

Exponent: TypeAlias = tuple[Q, ...]
Form: TypeAlias = dict[Exponent, Q]


def clean(f: Form) -> Form:
    return {e: a for e, a in f.items() if a}


def plus_exp(a: Exponent, b: Exponent) -> Exponent:
    if len(a) != len(b):
        raise ValueError("Exponent dimensions must match")
    return tuple(x + y for x, y in zip(a, b))


def scale_exp(a: Exponent, scalar: Q) -> Exponent:
    return tuple(scalar * x for x in a)


def add(f: Form, g: Form) -> Form:
    out = dict(f)
    for e, a in g.items():
        out[e] = out.get(e, Q(0)) + a
    return clean(out)


def mul(f: Form, g: Form) -> Form:
    out: Form = {}
    for a, x in f.items():
        for b, y in g.items():
            e = plus_exp(a, b)
            out[e] = out.get(e, Q(0)) + x * y
    return clean(out)


def derivative(f: Form, coordinate: int) -> Form:
    # A coordinate of an exponent is an additive functional on the exponent group.
    return clean({e: a * e[coordinate] for e, a in f.items()})


def truncated_mul(f: list[Q], g: list[Q], order: int) -> list[Q]:
    out = [Q(0) for _ in range(order + 1)]
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            if i + j <= order:
                out[i + j] += a * b
    return out


def binomial_coefficients(alpha: Q, order: int) -> list[Q]:
    out = [Q(1)]
    for n in range(order):
        out.append(out[-1] * (alpha - n) / (n + 1))
    return out


def main() -> None:
    rng = Random(20260922)
    counts: Counter[str] = Counter()
    zero = (Q(0), Q(0))
    c = (Q(1), Q(0))

    # In lexicographic Q^2, (0,a) is smaller than c/n for every positive n.
    # Check finite versions of the telescoping identity, retaining the remainder.
    for b_num in range(1, 9):
        for h_num in range(1, 5):
            a = (Q(0), Q(b_num + h_num, 3))
            b = (Q(0), Q(b_num, 3))
            h = plus_exp(a, scale_exp(b, Q(-1)))
            for length in range(1, 11):
                q: Form = {}
                for n in range(length):
                    e = plus_exp(plus_exp(c, scale_exp(a, Q(-1))),
                                 scale_exp(h, Q(-n)))
                    assert e > zero, "A finite witness exponent was not positive"
                    q[e] = Q(1)
                actual = mul({a: Q(1), b: Q(-1)}, q)
                remainder = plus_exp(c, scale_exp(h, Q(-length)))
                expected = {c: Q(1), remainder: Q(-1)}
                assert actual == expected, "Finite telescoping identity failed"
                counts["finite telescoping identities (positive supports)"] += 1

    candidates = [(Q(a), Q(b, 2))
                  for a in range(3) for b in range(-4, 5)
                  if (Q(a), Q(b, 2)) > zero]

    def random_form() -> Form:
        f: Form = {zero: Q(rng.randint(-8, 8))}
        for e in rng.sample(candidates, 8):
            f[e] = Q(rng.randint(-8, 8), rng.randint(1, 5))
        return clean(f)

    for _ in range(300):
        f, g = random_form(), random_form()
        fg = mul(f, g)
        assert fg.get(zero, Q(0)) == f.get(zero, Q(0)) * g.get(zero, Q(0))
        counts["constant-coefficient multiplicativity"] += 1
        for k in range(2):
            assert derivative(fg, k) == add(mul(derivative(f, k), g),
                                              mul(f, derivative(g, k)))
            counts["coordinate Hahn Leibniz identities"] += 1

    order = 20
    for m in range(2, 21):
        coeffs = binomial_coefficients(Q(1, m), order)
        power = [Q(1)] + [Q(0)] * order
        for _ in range(m):
            power = truncated_mul(power, coeffs, order)
        expected = [Q(1), Q(1)] + [Q(0)] * (order - 1)
        assert power == expected, "Truncated binomial power failed"
        counts["binomial m-th powers through order 20"] += 1

    for k in range(3):
        for j in range(3):
            exponent = tuple(Q(int(i == j)) for i in range(3))
            monomial = {exponent: Q(1)}
            expected = monomial if k == j else {}
            assert derivative(monomial, k) == expected
            counts["diagonal coordinate-derivation tests"] += 1

    for m in range(2, 31):
        first_negative_exponent = Q(1, m) - 1
        correction = binomial_coefficients(Q(1, m), 1)[1]
        assert first_negative_exponent < 0 and correction != 0
        counts["nonzero first negative root-correction terms"] += 1

    print("Exact finite checks: all passed")
    for name, count in counts.items():
        print(f"  {count:4d}  {name}")
    print(f"TOTAL: {sum(counts.values())} finite test cases")
    print("Arithmetic: fractions.Fraction; deterministic seed 20260922.")
    print("No infinite sum, class theorem, or cardinal construction is certified by these tests.")


if __name__ == "__main__":
    main()
