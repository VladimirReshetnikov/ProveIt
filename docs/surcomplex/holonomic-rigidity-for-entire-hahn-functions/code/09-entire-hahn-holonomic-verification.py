#!/usr/bin/env python3
"""Finite exact checks accompanying article.tex (Python 3.9+, standard library).

These checks validate formulas and finite valuation comparisons. They do NOT
prove the infinite summability, eventuality, or nonexistence theorems.
Run: python verification.py [--output PATH]
"""
from __future__ import annotations

import argparse
import math
import random
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

# Laurent polynomials in one commuting formal symbol, represented exactly.
LP = Dict[int, Fraction]
ZERO: LP = {}
ONE: LP = {0: Fraction(1)}
COUNTS: Dict[str, int] = defaultdict(int)


def clean(p: Mapping[int, Fraction]) -> LP:
    return {int(e): Fraction(c) for e, c in p.items() if c}


def mono(e: int = 0, c: Fraction = Fraction(1)) -> LP:
    return {e: Fraction(c)} if c else {}


def add(*terms: Mapping[int, Fraction]) -> LP:
    result: Dict[int, Fraction] = defaultdict(Fraction)
    for p in terms:
        for e, c in p.items():
            result[e] += c
    return clean(result)


def scale(p: Mapping[int, Fraction], c: Fraction) -> LP:
    return clean({e: c * v for e, v in p.items()})


def shift(p: Mapping[int, Fraction], e: int) -> LP:
    return {k + e: c for k, c in p.items()}


def mul(p: Mapping[int, Fraction], q: Mapping[int, Fraction]) -> LP:
    result: Dict[int, Fraction] = defaultdict(Fraction)
    for e, a in p.items():
        for f, b in q.items():
            result[e + f] += a * b
    return clean(result)


def power(p: Mapping[int, Fraction], n: int) -> LP:
    if n < 0:
        raise ValueError("power() requires a nonnegative integer")
    result = ONE.copy()
    b = dict(p)
    while n:
        if n & 1:
            result = mul(result, b)
        b = mul(b, b)
        n >>= 1
    return result


def val(p: Mapping[int, Fraction]) -> int:
    if not p:
        raise ValueError("Zero has no finite valuation")
    return min(p)


def check(group: str, condition: bool, detail: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] += 1


# An operator is {(operator power j, z degree k): scalar Laurent polynomial}.
Operator = Dict[Tuple[int, int], LP]


def q_action(op: Operator, a: Sequence[LP]) -> Dict[int, LP]:
    """Apply sum p_jk(q) z^k sigma_q^j to a finite series."""
    result: Dict[int, LP] = {}
    for (j, k), p in op.items():
        for n, an in enumerate(a):
            result[n + k] = add(result.get(n + k, {}), mul(p, shift(an, j * n)))
    return result


def falling(n: int, j: int) -> int:
    return math.prod(range(n - j + 1, n + 1))


def d_action(op: Operator, a: Sequence[LP]) -> Dict[int, LP]:
    """Apply sum p_jk(t) z^k D^j to a finite series, with D(t)=0."""
    result: Dict[int, LP] = {}
    for (j, k), p in op.items():
        for n in range(j, len(a)):
            degree = n - j + k
            term = scale(mul(p, a[n]), Fraction(falling(n, j)))
            result[degree] = add(result.get(degree, {}), term)
    return result


def theta_checks() -> None:
    nmax = 45
    theta = [mono(n * (n - 1) // 2) for n in range(nmax + 1)]
    positive: Operator = {(0, 0): ONE, (1, 0): mono(0, -1),
                          (1, 1): mono(0, -1), (2, 1): mono(1)}
    out = q_action(positive, theta)
    for n in range(nmax + 1):
        check("theta homogeneous, positive valuation", out.get(n, {}) == {}, f"degree {n}")
    inverse = [mono(-n * (n - 1) // 2) for n in range(nmax + 1)]
    negative: Operator = {(2, 0): ONE, (1, 0): mono(0, -1),
                          (1, 1): mono(2, -1), (0, 1): mono(1)}
    out = q_action(negative, inverse)
    for n in range(nmax + 1):
        check("theta homogeneous, negative valuation", out.get(n, {}) == {}, f"degree {n}")
    for n in range(1, nmax + 1):
        check("theta first-order coefficient recurrence", theta[n] == shift(theta[n-1], n-1), str(n))


def conversion_checks() -> None:
    op: Operator = {(0, 0): add(mono(-2, 3), mono(4)),
                    (1, 1): add(mono(1, 2), mono(3, -1)),
                    (2, 4): mono(-1, 5), (3, 2): mono(2, -2),
                    (0, 4): mono(6), (2, 0): mono(0, -7)}
    a = [add(mono(n*n, n+1), mono(-n-1, (-1)**n)) for n in range(50)]
    direct = q_action(op, a)
    degrees = {k for _, k in op}
    d, lo = max(degrees), min(degrees)
    for n in range(40):
        rhs = {}
        for h in range(d-lo+1):
            k = d-h
            r_at_qn = {}
            for (j, degree), scalar in op.items():
                if degree == k:
                    r_at_qn = add(r_at_qn, shift(scalar, j*(n+h)))
            rhs = add(rhs, mul(r_at_qn, a[n+h]))
        check("q-operator forward recurrence conversion", direct[n+d] == rhs, str(n))

    dop: Operator = {(0, 3): mono(2, 5), (1, 1): mono(-1, 3),
                     (3, 1): add(mono(4), mono(0, -2)),
                     (2, 2): mono(1, -4), (1, 4): mono(-2, 7)}
    direct_d = d_action(dop, a)
    ell0, ell1 = min(j-k for j, k in dop), max(j-k for j, k in dop)
    for n in range(4, 36):
        m = n-ell0
        rhs = {}
        for h in range(ell1-ell0+1):
            ell = ell0+h
            ch = {}
            for (j, k), scalar in dop.items():
                if j-k == ell:
                    ch = add(ch, scale(scalar, Fraction(falling(n+h, j))))
            rhs = add(rhs, mul(ch, a[n+h]))
        check("D-operator forward recurrence conversion", direct_d.get(m, {}) == rhs, str(n))


def unit_checks() -> None:
    u = add(ONE, mono(1))
    q = scale(u, Fraction(-1))
    for n in range(1, 61):
        qn_minus_one = add(power(q, n), mono(0, -1))
        expected = 0 if n % 2 else 1
        check("unit orbit parity", val(qn_minus_one) == expected, str(n))
        p = add(power(u, n), mono(0, -1), mono(1, -3))
        check("unit orbit exceptional cancellation", val(p) == (2 if n == 3 else 1), str(n))

    # Test the full residue-polynomial formula with finite arbitrary tails.
    rng = random.Random(20260922)
    for case in range(12):
        coeffs = [clean({e: Fraction(rng.randint(-3, 3)) for e in range(-2, 4)})
                  for _ in range(4)]
        if not any(coeffs):
            continue
        for r in (0, 1):
            qr = power(q, r)
            b: List[LP] = []
            for j in range(4):
                terms = [scale(mul(coeffs[l], power(qr, l)), Fraction(math.comb(l, j)))
                         for l in range(j, 4)]
                b.append(add(*terms))
            alpha = min(val(bj)+j for j, bj in enumerate(b) if bj)
            active = {j: bj[val(bj)] * (2**j)
                      for j, bj in enumerate(b) if bj and val(bj)+j == alpha}
            for k in range(1, 17):
                n = r+2*k
                qn = power(q, n)
                p_at = add(*(mul(bj, power(qn, j)) for j, bj in enumerate(coeffs)))
                h = sum(c * (k**j) for j, c in active.items())
                if h:
                    check("unit orbit residue-polynomial formula", bool(p_at) and val(p_at) == alpha,
                          f"case={case}, r={r}, k={k}")
                else:
                    check("unit orbit residue-polynomial cancellation", not p_at or val(p_at) > alpha,
                          f"case={case}, r={r}, k={k}")


Vec = Tuple[Fraction, ...]


def vec(*coords: int) -> Vec:
    return tuple(Fraction(c) for c in coords)


def vadd(a: Vec, b: Vec) -> Vec:
    size = max(len(a), len(b))
    return tuple((a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0) for i in range(size))


def vmul(n: Fraction, a: Vec) -> Vec:
    return tuple(n*x for x in a)


def vcmp(a: Vec, b: Vec) -> int:
    delta = vadd(a, vmul(Fraction(-1), b))
    for c in reversed(delta):
        if c:
            return 1 if c > 0 else -1
    return 0


def basis(n: int) -> Vec:
    return tuple(Fraction(int(j == n)) for j in range(n+1))


def valuation_checks() -> None:
    e0, e1, zero = vec(1, 0), vec(0, 1), vec(0, 0)
    for n in range(1, 201):
        check("rank-two noncofinal affine minimum", vcmp(vmul(n, e0), e1) < 0, str(n))
        check("theta excluded upper-scale argument", vcmp(vadd(vmul(n, e0), vmul(-1, e1)), zero) < 0, str(n))
    for depth in (0, 1, 2, 7, 23):
        delta = vmul(-depth, e0)
        for n in range(depth+1, depth+35):
            increment = vadd(vmul(n, e0), delta)
            check("theta included coarse boundary", vcmp(increment, zero) > 0 and increment[1] == 0,
                  f"depth={depth}, n={n}")
    # At a top-scale dilation, finitely many integer multiples dominate delta.
    for a0 in (-17, 0, 31):
        for a1 in (-8, -1, 0, 3):
            delta = vec(a0, a1)
            for n in range(max(1, -a1+1), max(1, -a1+1)+10):
                check("theta cofinal-scale growth", vcmp(vadd(vmul(n, e1), delta), zero) > 0, str((delta, n)))

    rng = random.Random(41519)
    for size in range(1, 6):
        for _ in range(12):
            delta = tuple(Fraction(rng.randint(-20, 20), rng.randint(1, 7)) for _ in range(size))
            for n in range(size+1, size+9):
                hn = vadd(basis(n), vmul(n, delta))
                hn1 = vadd(basis(n+1), vmul(n+1, delta))
                check("finite-coordinate entire witness growth", vcmp(hn, ()) > 0 and vcmp(hn1, hn) > 0,
                      str((delta, n)))

    # Sparse recurrence t^3 a_n + a_(n+2)=0, a_0=1, a_1=0.
    a = [ONE.copy(), {}]
    for n in range(50):
        a.append(scale(shift(a[n], 3), Fraction(-1)))
    for n in range(50):
        check("sparse recurrence exact identity", add(shift(a[n], 3), a[n+2]) == {}, str(n))
    bound = Fraction(3, 2)
    for n in range(0, 50, 2):
        check("escape boundary constant leading exponent", Fraction(val(a[n]))-n*bound == 0, str(n))
        check("escape strict exterior descent",
              Fraction(val(a[n+2]))-(n+2)*(bound+1) < Fraction(val(a[n]))-n*(bound+1), str(n))

    for n in range(1, 61):
        an = mono(2*n, Fraction(1, math.factorial(n)))
        prev = mono(2*(n-1), Fraction(1, math.factorial(n-1)))
        check("formal exponential recurrence", scale(an, Fraction(n)) == shift(prev, 2), str(n))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional path for a copy of the check report")
    args = parser.parse_args()
    theta_checks()
    conversion_checks()
    unit_checks()
    valuation_checks()
    lines = ["FINITE EXACT CHECKS -- Entire Hahn Functions and Holonomic Rigidity", ""]
    lines.extend(f"PASS  {count:4d}  {name}" for name, count in COUNTS.items())
    lines.extend(["", f"TOTAL: {sum(COUNTS.values())} checks passed; 0 failed.",
                  "Arithmetic: integers, Fraction, finite Laurent polynomials, lexicographic vectors.",
                  "Seeds: 20260922 and 41519. No external libraries or network access.",
                  "", "LIMITATION: This is not formal verification of any infinite theorem.",
                  "No finite truncation proves strong summability, eventuality, cofinality,",
                  "or universal nonexistence of a differential/dilation equation."])
    report = "\n".join(lines) + "\n"
    print(report, end="")
    if args.output:
        args.output.write_text(report, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
