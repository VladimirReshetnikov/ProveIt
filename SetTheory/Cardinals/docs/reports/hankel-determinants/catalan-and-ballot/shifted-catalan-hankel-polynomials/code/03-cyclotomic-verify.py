#!/usr/bin/env python3
"""Exact audits for cyclotomic Catalan Hankel recurrences.

Python 3.10+; standard library only. No floating point, CAS, network, or
unproved recurrence inference is used. The universal proofs are in article.tex.
Run from any directory: python3 code/verify.py [--quick] [--output PATH]
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence


def sign(n: int) -> int:
    return -1 if n % 2 else 1


def trim(p: list[int]) -> list[int]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def exact_monic_div(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    """Divide integer polynomials (ascending coefficient order), exactly."""
    if not b or b[-1] != 1:
        raise ValueError("The divisor must be monic.")
    r = list(a)
    q = [0] * max(1, len(a) - len(b) + 1)
    for j in range(len(a) - len(b), -1, -1):
        c = r[j + len(b) - 1]
        q[j] = c
        for i, x in enumerate(b):
            r[j + i] -= c * x
    if any(r):
        raise ArithmeticError("Polynomial division had a nonzero remainder.")
    return tuple(trim(q))


@lru_cache(None)
def cyclotomic(m: int) -> tuple[int, ...]:
    if m < 1:
        raise ValueError("Cyclotomic order must be positive.")
    p = [-1] + [0] * (m - 1) + [1]
    for d in range(1, m):
        if m % d == 0:
            p = list(exact_monic_div(p, cyclotomic(d)))
    return tuple(p)


class CyclotomicRing:
    """Z[z]/Phi_m(z), represented by tuples of exact integer coefficients."""

    def __init__(self, m: int):
        self.m = m
        self.phi = cyclotomic(m)
        self.degree = len(self.phi) - 1
        self.zero = (0,) * self.degree
        self.one = (1,) + (0,) * (self.degree - 1)
        self.z = self.reduce([0, 1])
        powers = [self.one]
        for _ in range(1, m):
            powers.append(self.mul(powers[-1], self.z))
        self.powers = tuple(powers)
        if self.mul(powers[-1], self.z) != self.one:
            raise ArithmeticError("Cyclotomic generator did not have the stated order.")

    def reduce(self, p: Sequence[int]) -> tuple[int, ...]:
        a = list(p) + [0] * max(0, self.degree - len(p))
        for j in range(len(a) - 1, self.degree - 1, -1):
            c = a[j]
            if c:
                for i in range(self.degree):
                    a[j - self.degree + i] -= c * self.phi[i]
        return tuple(a[:self.degree])

    def add(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return tuple(x + y for x, y in zip(a, b))

    def scale(self, a: Sequence[int], c: int) -> tuple[int, ...]:
        return tuple(c * x for x in a)

    def sub(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return tuple(x - y for x, y in zip(a, b))

    def mul(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        p = [0] * (2 * self.degree - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        p[i + j] += x * y
        return self.reduce(p)

    def pow(self, a: Sequence[int], n: int) -> tuple[int, ...]:
        if n < 0:
            raise ValueError("Only nonnegative general powers are implemented.")
        ans = self.one
        b = tuple(a)
        while n:
            if n & 1:
                ans = self.mul(ans, b)
            b = self.mul(b, b)
            n >>= 1
        return ans

    def zp(self, n: int) -> tuple[int, ...]:
        return self.powers[n % self.m]

    def integer(self, n: int) -> tuple[int, ...]:
        return self.scale(self.one, n)


def product_linear(constants: Iterable[int]) -> tuple[int, ...]:
    """Coefficients of product(2*N+c), in ascending order."""
    p = [1]
    for c in constants:
        q = [0] * (len(p) + 1)
        for j, x in enumerate(p):
            q[j] += c * x
            q[j + 1] += 2 * x
        p = q
    return tuple(p)


@lru_cache(None)
def subset_terms(t: int) -> tuple[tuple[int, int, int, tuple[int, ...]], ...]:
    """Return (k, z_exponent, integer_factor, polynomial) for all subsets."""
    T = t * (t - 1) // 2
    terms = []
    for k in range(t + 1):
        for S in itertools.combinations(range(t), k):
            C = tuple(j for j in range(t) if j not in S)
            sigma = sum(S)
            factor = sign(T + t - k - sigma)
            factor *= math.prod(j - i for i, j in itertools.combinations(S, 2))
            factor *= math.prod(j - i for i, j in itertools.combinations(C, 2))
            p = product_linear(i + j + 1 for i in S for j in C)
            terms.append((k, 2 * sigma + k - T, factor, p))
    return tuple(terms)


def raw_sectors(t: int, ring: CyclotomicRing) -> list[list[tuple[int, ...]]]:
    """F_k = P_k / K_t: division-free cyclotomic polynomial coefficients."""
    out = [[ring.zero] * (k * (t - k) + 1) for k in range(t + 1)]
    for k, e, f, p in subset_terms(t):
        v = ring.scale(ring.zp(e), f)
        for j, a in enumerate(p):
            if a:
                out[k][j] = ring.add(out[k][j], ring.scale(v, a))
    return out


def poly_degree(p: Sequence[Sequence[int]]) -> int:
    for j in range(len(p) - 1, -1, -1):
        if any(p[j]):
            return j
    return -1


def poly_eval(p: Sequence[Sequence[int]], n: int,
              ring: CyclotomicRing) -> tuple[int, ...]:
    ans = ring.zero
    for c in reversed(p):
        ans = ring.add(ring.scale(ans, n), c)
    return ans


def affine_reflection(p: Sequence[Sequence[int]], t: int,
                      ring: CyclotomicRing) -> list[tuple[int, ...]]:
    """Coefficients of p(-N-t), without division."""
    out = [ring.zero] * len(p)
    for j, c in enumerate(p):
        for r in range(j + 1):
            factor = sign(j) * math.comb(j, r) * t ** (j - r)
            out[r] = ring.add(out[r], ring.scale(c, factor))
    return out


def predicted_exponents(t: int, ring: CyclotomicRing) -> dict[int, int]:
    """Map k mod L to minimal multiplicity; zero means the rate disappears."""
    L = ring.m // math.gcd(ring.m, 2)
    labels = sorted({k % L for k in range(t + 1)})
    if L == 2 and t % 2 == 0:
        m = t // 2
        return {r: (m * m + 1 if r == m % 2 else 0) for r in labels}
    out = {r: max(k * (t - k) for k in range(r, t + 1, L)) + 1
           for r in labels}
    if L == 2:  # odd central powers
        return out
    if L <= t and (t - L) % 2 == 0:
        k = (t - L) // 2
        rho = ring.scale(ring.zp(L * t), sign(L * (t + 1) // 2))
        if rho == ring.scale(ring.one, -1):
            out[k % L] -= 1
    return out


def closed_order(t: int, ring: CyclotomicRing) -> int:
    L = ring.m // math.gcd(ring.m, 2)
    if L == 2:
        return t * t // 4 + 1 if t % 2 == 0 else (t * t + 3) // 2
    if L > t:
        return t + 1 + math.comb(t + 1, 3)
    eta = int((t - L) % 2 == 0)
    numerator = L * (3 * t * t - L * L + 13 - 3 * eta)
    if numerator % 12:
        raise ArithmeticError("Order formula was nonintegral.")
    defect = 0
    if eta:
        rho = ring.scale(ring.zp(L * t), sign(L * (t + 1) // 2))
        defect = int(rho == ring.scale(ring.one, -1))
    return numerator // 12 - defect


def root_free_factors(t: int, c: Sequence[int], ring: CyclotomicRing
                      ) -> tuple[int | None, list[tuple[list[tuple[int, ...]], int]]]:
    """Minimal polynomial as linear/quadratic factors over the input field.

    No access to ring.m, z, or cyclotomic order is used. Only exact scalar
    arithmetic and equality tests on c are needed. Each polynomial is given
    in ascending coefficient order, followed by its positive exponent.
    """
    if t < 1:
        raise ValueError("Multiplicity must be positive.")
    if tuple(c) in (ring.zero, ring.integer(4)):
        raise ValueError("Endpoint roots c=0 and c=4 require a separate formula.")
    u = ring.sub(c, ring.integer(2))
    previous, current = ring.one, u
    L, sigma = None, None
    for candidate in range(2, t + 1):
        if current == ring.zero:
            L, sigma = candidate, ring.scale(previous, -1)
            break
        previous, current = current, ring.sub(ring.mul(u, current), previous)
    if L == 2:
        if t % 2 == 0:
            return L, [([ring.integer(-1), ring.one], t * t // 4 + 1)]
        return L, [([ring.one, ring.zero, ring.one], (t * t - 1) // 4 + 1)]
    bound = t if L is None else L - 1
    S = [ring.integer(2), u]
    for a in range(1, bound):
        S.append(ring.sub(ring.mul(u, S[-1]), S[-2]))
    factors = []
    if t % 2 == 0:
        factors.append(([ring.integer(-1), ring.one], t * t // 4 + 1))
    for a in range(1, bound + 1):
        if (a - t) % 2 == 0:
            factors.append(([ring.one, ring.scale(S[a], -sign(t)), ring.one],
                            (t * t - a * a) // 4 + 1))
    if L is not None and (L - t) % 2 == 0:
        assert sigma is not None
        rho = ring.scale(ring.pow(sigma, t), sign(L * (t + 1) // 2))
        defect = int(rho == ring.integer(-1))
        exponent = (t * t - L * L) // 4 + 1 - defect
        if exponent:
            factors.append(([ring.scale(sigma, -sign(t)), ring.one], exponent))
    return L, factors


def catalan(n: int) -> int:
    return math.comb(2 * n, n) // (n + 1)


def bareiss(matrix: Sequence[Sequence[int]]) -> int:
    """Fraction-free determinant with row pivoting; supports singular matrices."""
    n = len(matrix)
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    parity, previous = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            parity = -parity
        v = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = v * a[i][j] - a[i][k] * a[k][j]
                result, rem = divmod(numerator, previous)
                if rem:
                    raise ArithmeticError("Nonexact Bareiss division.")
                a[i][j] = result
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = v
    return parity * a[-1][-1]


def moment_hankel(t: int, c: int, n: int) -> int:
    mu = [sum(math.comb(t, r) * (-c) ** (t - r) * catalan(j + r)
              for r in range(t + 1)) for j in range(max(0, 2 * n - 1))]
    return bareiss([[mu[i + j] for j in range(n)] for i in range(n)])


def jet_hankel(t: int, c: int, n: int) -> int:
    if t == 0:
        return 1
    jets = [[1] + [0] * (t - 1), [c - 1] + [0] * (t - 1)]
    if t > 1:
        jets[1][1] = 1
    for j in range(1, n + t - 1):
        jets.append([(c - 2) * jets[j][r] - jets[j - 1][r]
                     + (jets[j][r - 1] if r else 0) for r in range(t)])
    return sign(n * t) * bareiss([[jets[n + j][r] for j in range(t)]
                                  for r in range(t)])


def rectangle(a: int, b: int, n: int) -> Fraction:
    ans = Fraction(1)
    for i in range(1, a + 1):
        for j in range(1, b + 1):
            ans *= Fraction(n + i + j - 1, i + j - 1)
    return ans


def central(t: int, n: int) -> Fraction:
    return sign(t * n * (n + 1) // 2) * rectangle(t // 2, (t + 1) // 2, n)


def ring_det(a: Sequence[Sequence[Sequence[int]]],
             ring: CyclotomicRing) -> tuple[int, ...]:
    """Independent Leibniz determinant; deliberately only used for N <= 4."""
    n = len(a)
    ans = ring.zero
    for perm in itertools.permutations(range(n)):
        term = ring.one
        for i in range(n):
            term = ring.mul(term, a[i][perm[i]])
        inv = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        ans = ring.add(ans, ring.scale(term, sign(inv)))
    return ans


def cyclotomic_hankel(t: int, n: int, ring: CyclotomicRing) -> tuple[int, ...]:
    c = ring.add(ring.integer(2), ring.add(ring.zp(1), ring.zp(-1)))
    neg_c = ring.scale(c, -1)
    powers = [ring.pow(neg_c, t - r) for r in range(t + 1)]
    moments = []
    for j in range(max(0, 2 * n - 1)):
        mu = ring.zero
        for r in range(t + 1):
            mu = ring.add(mu, ring.scale(powers[r], math.comb(t, r) * catalan(j + r)))
        moments.append(mu)
    return ring_det([[moments[i + j] for j in range(n)] for i in range(n)], ring)


def run(quick: bool, output: Path) -> dict:
    counts: Counter = Counter()
    rows = []

    def check(condition: bool, category: str, context: object = None) -> None:
        if not condition:
            raise AssertionError(f"{category}: {context}")
        counts[category] += 1

    max_t, max_m = (7, 14) if quick else (12, 24)
    for m in range(3, max_m + 1):
        ring = CyclotomicRing(m)
        qminus = ring.sub(ring.zp(2), ring.one)
        qplus = ring.add(ring.zp(2), ring.one)
        L = m // math.gcd(m, 2)
        for t in range(1, max_t + 1):
            sectors = raw_sectors(t, ring)
            T = t * (t - 1) // 2
            for k, p in enumerate(sectors):
                h, d = t - k, k * (t - k)
                check(poly_degree(p) == d, "sector_degrees", (m, t, k))
                # K_t times this expected raw leading coefficient is ell_{t,k}.
                expected = ring.scale(
                    ring.mul(ring.zp(k * k - T), ring.pow(qminus, d)),
                    sign(h * (h + 1) // 2) * 2 ** d
                    * math.prod(math.factorial(j) for j in range(k))
                    * math.prod(math.factorial(j) for j in range(h)))
                check(p[d] == expected, "leading_coefficients", (m, t, k))
                if d:
                    lhs = ring.mul(ring.sub(ring.scale(p[d - 1], 4),
                                              ring.scale(p[d], 2 * d * t)), qminus)
                    rhs = ring.scale(ring.mul(p[d], qplus), d * (h - k))
                    check(lhs == rhs, "first_centered_corrections", (m, t, k))
                factor = ring.scale(ring.zp((h - k) * t), sign(t * (t + 1) // 2))
                reflected = [ring.mul(factor, a) for a in affine_reflection(p, t, ring)]
                check(reflected == sectors[h], "sector_reflections", (m, t, k))
            expected_exp = predicted_exponents(t, ring)
            for r, e in expected_exp.items():
                grouped = [ring.zero] * (t * t // 4 + 1)
                for k in range(r, t + 1, L):
                    for j, a in enumerate(sectors[k]):
                        grouped[j] = ring.add(grouped[j], a)
                check(poly_degree(grouped) + 1 == e, "grouped_minimal_multiplicities",
                      (m, t, r, poly_degree(grouped), e))
            order = sum(expected_exp.values())
            check(order == closed_order(t, ring), "closed_order_formula", (m, t, order))
            c = ring.add(ring.integer(2), ring.add(ring.zp(1), ring.zp(-1)))
            detected, factors = root_free_factors(t, c, ring)
            check(detected == (L if L <= t else None), "root_free_resonance_detection", (m, t))
            check(sum((len(p) - 1) * e for p, e in factors) == order,
                  "root_free_factor_degrees", (m, t))
            for r, e in expected_exp.items():
                rate = ring.scale(ring.zp(2 * r - t), sign(t))
                multiplicity = 0
                for factor, exponent in factors:
                    value = ring.zero
                    for a in reversed(factor):
                        value = ring.add(ring.mul(value, rate), a)
                    if value == ring.zero:
                        multiplicity += exponent
                check(multiplicity == e, "root_free_factor_multiplicities", (m, t, r))
            rows.append({"primitive_z_order": m, "order_z_squared": L,
                         "root_multiplicity": t, "minimal_order": order,
                         "multiplicities_by_k_mod_L": expected_exp})
            if t <= (5 if quick else 8) and m <= 14:
                factor = ring.scale(ring.mul(ring.pow(qminus, T),
                                              ring.pow(ring.sub(ring.z, ring.one), t)),
                                    math.prod(math.factorial(j) for j in range(t)))
                for n in range(5):
                    left = ring.mul(cyclotomic_hankel(t, n, ring), factor)
                    total = ring.zero
                    for k, p in enumerate(sectors):
                        total = ring.add(total, ring.mul(poly_eval(p, n, ring),
                                                        ring.zp((2 * k - t) * n)))
                    right = ring.scale(ring.mul(ring.zp(T), total), sign(n * t))
                    check(left == right, "independent_cyclotomic_determinants", (m, t, n))
        print(f"Cyclotomic order {m}: passed", flush=True)

    for c in (-2, 0, 1, 2, 3, 4, 5):
        for t in range(1, (7 if quick else 10) + 1):
            for n in range(11):
                check(moment_hankel(t, c, n) == jet_hankel(t, c, n),
                      "original_vs_jet_determinants", (t, c, n))
    for t in range(0, (10 if quick else 16) + 1):
        for n in range(17):
            check(central(t, n) == jet_hankel(t, 2, n), "central_product", (t, n))
    for m in range(7):
        for n in range(1, 10):
            B = rectangle(m, m + 1, n) ** 2
            check(rectangle(m, m, n) * rectangle(m + 1, m + 1, n) / B
                  == Fraction(n + 2 * m + 1, 2 * m + 1), "condensation_ratios_even_A")
            check(rectangle(m, m, n + 1) * rectangle(m + 1, m + 1, n - 1) / B
                  == Fraction(n, 2 * m + 1), "condensation_ratios_even_B")
            B = rectangle(m + 1, m + 1, n) ** 2
            check(rectangle(m, m + 1, n) * rectangle(m + 1, m + 2, n) / B
                  == Fraction(n + 2 * m + 2, 2 * (n + m + 1)), "condensation_ratios_odd_A")
            check(rectangle(m, m + 1, n + 1) * rectangle(m + 1, m + 2, n - 1) / B
                  == Fraction(n, 2 * (n + m + 1)), "condensation_ratios_odd_B")

    # Two exact residue-class examples. Their universal validity also follows
    # from degree-two progression bounds plus finite quadratic interpolation.
    for N in range(60):
        n, r = divmod(N, 6)
        c1 = [(4 * n + 1) ** 2,
              (2 * n + 1) * (4 * n + 1),
              -(2 * n + 1) * (4 * n + 3),
              -(4 * n + 3) ** 2,
              -2 * (n + 1) * (4 * n + 3),
              2 * (n + 1) * (4 * n + 5)][r]
        n, r = divmod(N, 3)
        c3 = [2 * n + 1, -(n + 1) * (18 * n + 13),
              (n + 1) * (18 * n + 23)][r]
        check(jet_hankel(3, 1, N) == c1, "worked_residue_formulas_c1")
        check(jet_hankel(3, 3, N) == c3, "worked_residue_formulas_c3")

    # Extra tests of the elementary sign classification and square-sum formula.
    for m in range(3, 61):
        ring = CyclotomicRing(m)
        L = m // math.gcd(m, 2)
        for t in range(1, 101):
            if L > t:
                continue
            eta = int((t - L) % 2 == 0)
            ds = [min((2 * k - t) ** 2 for k in range(r, t + 1, L))
                  for r in range(L)]
            check(sum(ds) == L * (L * L - 1) // 3 + L * eta,
                  "centered_square_sum", (m, t))
            if L == 2:
                continue
            direct = 0
            simplified = 0
            if eta:
                rho = ring.scale(ring.zp(L * t), sign(L * (t + 1) // 2))
                direct = int(rho == ring.scale(ring.one, -1))
                if L % 2 == 0:
                    simplified = int(L % 4 == 2)
                else:
                    simplified = int(ring.zp(L) == ring.integer(sign((t - 1) // 2)))
            check(direct == simplified, "simplified_defect_sign", (m, t))

    output.mkdir(parents=True, exist_ok=True)
    result = {"status": "PASS", "arithmetic": "exact integers and cyclotomic integer quotients",
              "quick": quick, "max_sector_multiplicity": max_t,
              "max_primitive_z_order": max_m,
              "counts": dict(sorted(counts.items())), "total_checks": sum(counts.values())}
    (output / "verification_summary.json").write_text(json.dumps(result, indent=2) + "\n")
    (output / "cyclotomic_orders.json").write_text(json.dumps(rows, indent=2) + "\n")
    with (output / "orders_c1_c2_c3.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["t", "c1_order", "c2_order", "c3_order", "generic_order"])
        for t in range(1, 21):
            writer.writerow([t, closed_order(t, CyclotomicRing(3)),
                             closed_order(t, CyclotomicRing(4)),
                             closed_order(t, CyclotomicRing(6)),
                             t + 1 + math.comb(t + 1, 3)])
    print(json.dumps(result, indent=2), flush=True)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="Use smaller main parameter grids.")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    run(args.quick, args.output)


if __name__ == "__main__":
    main()
