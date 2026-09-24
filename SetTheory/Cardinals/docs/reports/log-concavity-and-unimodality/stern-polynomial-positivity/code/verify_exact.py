#!/usr/bin/env python3
"""Exact, dependency-free checks for the Stern-polynomial research note.

Polynomials are tuples of integer coefficients in increasing degree order.
The primary evaluator uses the binary expansion of the *Stern index*, not the
second-order recurrence for the special family.  No floating point is used.
Finite checks supplement, but do not replace, the universal proofs in the note.

Run: python3 code/verify_exact.py --out results/exact_verification.json
"""
from __future__ import annotations
import argparse
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path
from typing import Sequence

Poly = tuple[int, ...]
ZERO: Poly = (0,)
ONE: Poly = (1,)
T: Poly = (0, 1)


def trim(p: Sequence[int]) -> Poly:
    q = list(p) or [0]
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return tuple(q)


def add(p: Poly, q: Poly) -> Poly:
    a = [0] * max(len(p), len(q))
    for i, c in enumerate(p):
        a[i] += c
    for i, c in enumerate(q):
        a[i] += c
    return trim(a)


def scale(p: Poly, k: int) -> Poly:
    return trim([k * c for c in p])


def sub(p: Poly, q: Poly) -> Poly:
    return add(p, scale(q, -1))


def shift(p: Poly, k: int = 1) -> Poly:
    if k < 0:
        raise ValueError("The shift must be nonnegative")
    return ZERO if p == ZERO else (0,) * k + p


def mul(p: Poly, q: Poly) -> Poly:
    if p == ZERO or q == ZERO:
        return ZERO
    a = [0] * (len(p) + len(q) - 1)
    for i, c in enumerate(p):
        for j, d in enumerate(q):
            a[i + j] += c * d
    return trim(a)


def stern_pair(index: int) -> tuple[Poly, Poly]:
    """Return (B_index, B_(index+1)) using binary-digit transitions."""
    if index < 0:
        raise ValueError("The Stern index must be nonnegative")
    p, q = ZERO, ONE
    for bit in bin(index)[2:]:
        if bit == "0":
            p, q = shift(p), add(p, q)
        else:
            p, q = add(p, q), shift(q)
    return p, q


def stern(index: int) -> Poly:
    return stern_pair(index)[0]


def a_index(n: int) -> int:
    return (4**n - 1) // 3


def h_index(n: int) -> int:
    return 2 * (4**n - 1) * (2 * 4**n + 1) // 3 + 1


def a_binomial(n: int) -> Poly:
    if n == 0:
        return ZERO
    return tuple(math.comb(2 * n - 1 - j, j) for j in range(n))


def norm_form(a: Poly, b: Poly) -> Poly:
    """b^2 - t*a*b + t^2*a^2."""
    return add(sub(mul(b, b), shift(mul(a, b))), shift(mul(a, a), 2))


def is_power_of_three(m: int) -> bool:
    if m < 1:
        return False
    while m % 3 == 0:
        m //= 3
    return m == 1


def sturm_real_root_count(p: Poly) -> int:
    """Number of distinct real roots, via exact rational Sturm remainders."""
    def qtrim(a: Sequence[Fraction]) -> list[Fraction]:
        b = list(a) or [Fraction(0)]
        while len(b) > 1 and b[-1] == 0:
            b.pop()
        return b

    def remainder(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
        r = list(a)
        while len(r) >= len(b) and r != [0]:
            k, c = len(r) - len(b), r[-1] / b[-1]
            for j, d in enumerate(b):
                r[k + j] -= c * d
            r = qtrim(r)
        return r

    f = [Fraction(c) for c in p]
    g = [Fraction(i * p[i]) for i in range(1, len(p))]
    if not g:
        return 0
    chain = [f, qtrim(g)]
    while True:
        r = [-c for c in remainder(chain[-2], chain[-1])]
        if r == [0]:
            break
        # A positive normalization preserves signs in a Sturm chain.
        magnitude = abs(r[-1])
        chain.append([c / magnitude for c in r])

    def variations(at_minus_infinity: bool) -> int:
        signs = []
        for f in chain:
            sg = 1 if f[-1] > 0 else -1
            if at_minus_infinity and (len(f) - 1) % 2:
                sg *= -1
            signs.append(sg)
        return sum(a != b for a, b in zip(signs, signs[1:]))
    return variations(True) - variations(False)


def run_checks(max_n: int = 160, sturm_n: int = 12) -> dict:
    if max_n < 3 or sturm_n < 0 or sturm_n > max_n:
        raise ValueError("Require max_n >= 3 and 0 <= sturm_n <= max_n")
    t0 = time.perf_counter()
    counts: dict[str, int] = {}
    total = 0

    def check(ok: bool, group: str, detail: str) -> None:
        nonlocal total
        if not ok:
            raise AssertionError(f"{group}: {detail}")
        counts[group] = counts.get(group, 0) + 1
        total += 1

    # A simple direct recurrence is independent of binary-pair evaluation.
    direct = [ZERO, ONE]
    for k in range(2, 1025):
        direct.append(shift(direct[k // 2]) if k % 2 == 0
                      else add(direct[k // 2], direct[k // 2 + 1]))
    for k, p in enumerate(direct):
        check(stern(k) == p, "binary_evaluator_vs_direct", str(k))

    # Independent hyperbinary generating-product expansion, truncated at x^64.
    limit = 64
    product = [ZERO for _ in range(limit + 1)]
    product[0] = ONE
    weight = 1
    while weight <= limit:
        nxt = list(product)
        for k, p in enumerate(product):
            if k + weight <= limit:
                nxt[k + weight] = add(nxt[k + weight], shift(p))
            if k + 2 * weight <= limit:
                nxt[k + 2 * weight] = add(nxt[k + 2 * weight], p)
        product = nxt
        weight *= 2
    for k, p in enumerate(product):
        check(p == stern(k + 1), "hyperbinary_generating_product", str(k))

    # Endpoints included: the concatenation identity must also hold at r = 2^k.
    for k in range(7):
        q = 2**k
        for m in range(25):
            for r in range(q + 1):
                rhs = add(mul(stern(q - r), stern(m)),
                          mul(stern(r), stern(m + 1)))
                check(stern(q * m + r) == rhs, "concatenation", f"{k},{m},{r}")

    A = [ZERO, ONE]
    for _ in range(max_n):
        A.append(sub(mul((1, 2), A[-1]), shift(A[-2], 2)))
    F = [ZERO, ONE]
    for _ in range(2 * max_n + 1):
        F.append(add(F[-1], shift(F[-2])))
    W: list[Poly] = []
    samples = []
    p = (1, 4, 3)
    for n in range(max_n + 1):
        a, c = stern_pair(a_index(n))
        b = A[n + 1]
        w = stern(h_index(n))
        W.append(w)
        check(a == A[n], "A_stern_vs_second_order", str(n))
        check(a == a_binomial(n), "A_stern_vs_binomial", str(n))
        check(b == add(mul((1, 1), a), c), "adjacent_conversion", str(n))
        quadratic = add(add(mul((1, 1, 1), mul(a, a)),
                            mul((2, 1), mul(a, c))), mul(c, c))
        check(w == quadratic, "original_quadratic_identity", str(n))
        check(w == norm_form(a, b), "corrected_norm_identity", str(n))
        sos = add(mul(sub(scale(b, 2), shift(a)),
                      sub(scale(b, 2), shift(a))), scale(shift(mul(a, a), 2), 3))
        check(scale(w, 4) == sos, "sum_of_squares_identity", str(n))
        check(len(w) - 1 == 2 * n, "degree", str(n))
        check(w[-1] == n * n + n + 1, "leading_coefficient", str(n))
        check(w[0] == 1, "constant_coefficient", str(n))
        check(all(c > 0 for c in w), "positive_coefficients", str(n))
        square_minus_monomial = sub(mul((1, 1), mul(F[2*n+1], F[2*n+1])),
                                    shift(ONE, 2*n+1))
        check(w == square_minus_monomial, "Fibonacci_square_identity", str(n))
        m, power3 = 2*n+1, 1
        while m % 3 == 0:
            m //= 3
            power3 *= 3
        reduced = trim([c % 3 for c in w])
        check(len(reduced)-1 == 2*n+1-power3 and reduced[-1] == 1,
              "exact_degree_mod3", str(n))
        constant_mod3 = all(c % 3 == 0 for c in w[1:])
        check(constant_mod3 == is_power_of_three(2 * n + 1),
              "mod3_classification", str(n))
        if n >= 3:
            rhs = add(sub(mul(p, W[n - 1]), shift(mul(p, W[n - 2]), 2)),
                      shift(W[n - 3], 6))
            check(w == rhs, "third_order_and_generating_function", str(n))
        if n <= 8:
            samples.append({"n": n, "h_n": str(h_index(n)),
                            "coefficients_ascending": list(w)})

    check(sub(W[1], mul(p, W[0])) == (0, -1), "GF_numerator", "u^1")
    check(add(sub(W[2], mul(p, W[1])), shift(mul(p, W[0]), 2)) == (0, 0, 0, 0, 1),
          "GF_numerator", "u^2")

    eisenstein = []
    for r in range(1, 7):
        n = (3**r - 1) // 2
        w = stern(h_index(n))
        check(w == norm_form(a_binomial(n), a_binomial(n + 1)),
              "large_subfamily_norm", str(n))
        check(w[0] == 1 and all(c % 3 == 0 for c in w[1:]) and w[-1] % 9 != 0,
              "reciprocal_Eisenstein_3", str(n))
        eisenstein.append({"r": r, "n": n, "degree": len(w) - 1,
                           "leading_coefficient": w[-1],
                           "Stern_index_bit_length": h_index(n).bit_length()})

    sturm = []
    # Check the root-count implementation on elementary control examples first.
    for polynomial, expected in [((1,), 0), ((1, 0, 1), 0),
                                 ((-1, 0, 1), 2), ((0, -1, 0, 1), 3),
                                 ((1, -2, 1), 1)]:
        check(sturm_real_root_count(polynomial) == expected, "Sturm_controls", str(polynomial))
    for n in range(1, sturm_n + 1):
        roots = sturm_real_root_count(W[n])
        check(roots == 0, "Sturm_no_real_roots", str(n))
        sturm.append({"n": n, "degree": 2 * n, "distinct_real_roots": roots})

    return {"status": "PASS", "arithmetic": "exact integers and rational numbers only",
            "python": platform.python_version(), "max_n": max_n,
            "checks_passed": total, "check_groups": counts,
            "eisenstein_cases": eisenstein, "sturm_cases": sturm,
            "sample_polynomials": samples,
            "runtime_seconds": round(time.perf_counter() - t0, 3),
            "scope": "Finite implementation audit; universal claims are proved in the paper."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=160)
    parser.add_argument("--sturm-n", type=int, default=12)
    parser.add_argument("--out", type=Path, default=Path("results/exact_verification.json"))
    args = parser.parse_args()
    report = run_checks(args.max_n, args.sturm_n)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("sample_polynomials", "eisenstein_cases", "sturm_cases")}, indent=2))
    print(f"Full report: {args.out}")


if __name__ == "__main__":
    main()
