#!/usr/bin/env python3
"""Exact finite checks for computable_surreal_numbers.tex.

Only rational arithmetic in finite truncation rings is used. These checks
are not a proof of the general theorems, a halting oracle, or a Lean audit.
Run with Python 3.10 or later; there are no third-party dependencies.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as Q
from math import factorial
from random import Random
from typing import Iterable

Series = list[Q]
N = 18                         # All dense calculations are modulo u**N.
COUNTS: dict[str, int] = defaultdict(int)


def check(group: str, condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] += 1


def series(values: Iterable[int | Q] = ()) -> Series:
    result = [Q(v) for v in values]
    return (result + [Q(0)] * N)[:N]


def add(a: Series, b: Series) -> Series:
    return [x + y for x, y in zip(a, b)]


def scale(a: Series, c: int | Q) -> Series:
    return [Q(c) * x for x in a]


def mul(a: Series, b: Series) -> Series:
    return [sum((a[j] * b[n-j] for j in range(n+1)), Q(0))
            for n in range(N)]


def inverse(a: Series) -> Series:
    if a[0] == 0:
        raise ValueError("The dense inverse needs a nonzero constant term.")
    b = series([1 / a[0]])
    for n in range(1, N):
        b[n] = -sum((a[j] * b[n-j] for j in range(1, n+1)), Q(0)) / a[0]
    return b


def compose(f: Series, g: Series) -> Series:
    if g[0] != 0:
        raise ValueError("Formal composition requires zero inner constant.")
    result, power = series(), series([1])
    for coefficient in f:
        result = add(result, scale(power, coefficient))
        power = mul(power, g)
    return result


def binomial(alpha: Q) -> Series:
    result = series([1])
    for n in range(1, N):
        result[n] = result[n-1] * (alpha - n + 1) / n
    return result


def polynomial_eval(coefficients: list[Series], y: Series) -> Series:
    result = series()
    for a in reversed(coefficients):
        result = add(mul(result, y), a)
    return result


def affine_reduction_lift(coefficients: list[Series], root0: Q,
                          slope: Q) -> Series:
    """Lift when F(0,Y) is affine with the supplied nonzero slope."""
    if slope == 0:
        raise ValueError("A nonzero reduced slope is required.")
    y = series([root0])
    if polynomial_eval(coefficients, y)[0] != 0:
        raise ValueError("The seed must solve the reduced equation.")
    for n in range(1, N):
        residual = polynomial_eval(coefficients, y)[n]
        y[n] = -residual / slope
    return y


def main() -> None:
    one, u = series([1]), series([0, 1])
    rng = Random(20260921)

    check("reciprocal", inverse(series([1, -1])) == series([1] * N),
          "geometric series")
    for _ in range(48):
        a = series(Q(rng.randint(-7, 7), rng.randint(1, 9))
                   for _ in range(rng.randint(1, N)))
        if a[0] == 0:
            a[0] = Q(3, 7)
        check("reciprocal", mul(a, inverse(a)) == one,
              "triangular inverse identity")

    sqrt1u = binomial(Q(1, 2))
    check("binomial", mul(sqrt1u, sqrt1u) == series([1, 1]),
          "square root of 1+u")
    cube = binomial(Q(1, 3))
    check("binomial", mul(mul(cube, cube), cube) == series([1, 1]),
          "cube root of 1+u")
    for _ in range(24):
        a = Q(rng.randint(-5, 5), rng.randint(1, 7))
        b = Q(rng.randint(-5, 5), rng.randint(1, 7))
        check("binomial", mul(binomial(a), binomial(b)) == binomial(a+b),
              "binomial exponent addition")

    expu = series(Q(1, factorial(n)) for n in range(N))
    log1u = series([0] + [Q((-1)**(n+1), n) for n in range(1, N)])
    check("formal functions", compose(expu, log1u) == series([1, 1]),
          "exp(log(1+u))")
    check("formal functions", compose(log1u, add(expu, scale(one, -1))) == u,
          "log(exp(u))")
    check("formal functions", mul(expu, compose(expu, scale(u, -1))) == one,
          "exp(u) exp(-u)")

    catalan = series([0, 1])
    for n in range(2, N):
        catalan[n] = sum((catalan[j] * catalan[n-j]
                          for j in range(1, n)), Q(0))
    check("implicit branches", add(add(catalan, scale(u, -1)),
                                   scale(mul(catalan, catalan), -1)) == series(),
          "Catalan polynomial")
    sqrt1minus4u = compose(sqrt1u, scale(u, -4))
    check("implicit branches", scale(add(one, scale(sqrt1minus4u, -1)),
                                     Q(1, 2)) == catalan,
          "Catalan closed form")
    check("implicit branches", catalan[1:7] == list(map(Q, [1, 1, 2, 5, 14, 42])),
          "displayed Catalan coefficients")

    # The finite-jet example f(Y)=Y^2-u^2(1+u).
    y = mul(u, sqrt1u)
    target = series([0, 0, 1, 1])
    check("finite jet", mul(y, y) == target, "positive derivative-valuation root")
    z = series(y[n+2] if n+2 < N else 0 for n in range(N))
    transformed = add(add(scale(one, -1), scale(z, 2)), mul(u, mul(z, z)))
    check("finite jet", transformed[:N-2] == [Q(0)] * (N-2),
          "transformed equation -1+2Z+uZ^2")
    check("finite jet", y[:6] == list(map(Q, [0, 1])) +
          [Q(1, 2), Q(-1, 8), Q(1, 16), Q(-5, 128)],
          "displayed finite-jet coefficients")

    # Random affine reductions with higher-u nonlinear coefficients.
    for _ in range(12):
        c = Q(rng.choice([-3, -2, -1, 1, 2, 3]), rng.randint(1, 5))
        a = Q(rng.randint(-3, 3), rng.randint(1, 5))
        coefficients = [series([-c*a]), series([c])]
        coefficients.extend([series(), series()])
        for row in coefficients:
            for n in range(1, 5):
                row[n] = Q(rng.randint(-2, 2), rng.randint(1, 5))
        lifted = affine_reduction_lift(coefficients, a, c)
        check("finite jet", polynomial_eval(coefficients, lifted) == series(),
              "triangular lift of an affine reduction")

    # Finite schedules stand in for known halting events. No undecidable
    # predicate is being evaluated or experimentally inferred here.
    for _ in range(12):
        events = {e: rng.randint(0, 9) for e in range(10)
                  if rng.randint(0, 1)}
        f_support = [Q(1) - Q(1, n+2) for n in range(10)]
        g_support = [Q(e) + Q(1, s+2) for e, s in events.items()]
        product: dict[Q, int] = defaultdict(int)
        for f in f_support:
            for g in g_support:
                product[f+g] += 1
        check("Hahn support arithmetic", all(count <= 1 for count in product.values()),
              "singleton-or-empty convolution fibers")
        for e in range(10):
            check("Hahn support arithmetic", product.get(Q(e+1), 0) == int(e in events),
                  "integer target detects its scheduled event")

    previous = Q(0)
    for n in range(1, 25):
        q = Q(n) + Q(1, 2**n)
        check("valuation example", q > previous and q > n and q.denominator == 2**n,
              "strict growth and unbounded reduced denominators")
        previous = q

    # Positive rational instances of the two branches in the oracle reduction.
    for j in range(1, 7):
        rootr = Q(1, 2**j)
        r = rootr**2
        inv = inverse(series([r, 1]))
        check("oracle-reduction identities", mul(series([r, 1]), inv) == one,
              "unit reciprocal has only integral nonnegative powers")
        root = scale(compose(sqrt1u, scale(u, 1/r)), rootr)
        check("oracle-reduction identities", mul(root, root) == series([r, 1]),
              "positive constant branch has integral powers")
    # The zero-constant branch has sqrt(t)=t^(1/2) and inverse t^(-1).
    check("oracle-reduction identities", Q(1, 2)+Q(1, 2) == 1,
          "ramified root exponent")
    check("oracle-reduction identities", Q(-1)+Q(1) == 0,
          "Laurent reciprocal exponent")

    print("Computable surreal numbers: exact finite verification")
    print(f"Dense formal-series precision: modulo u^{N}")
    print("Arithmetic: fractions.Fraction; random seed: 20260921")
    print("The checks do not prove the general theorems or decide halting.")
    print()
    for group, count in COUNTS.items():
        print(f"PASS  {group}: {count} checks")
    print()
    print(f"TOTAL: {sum(COUNTS.values())} passed; 0 failed")


if __name__ == "__main__":
    main()
