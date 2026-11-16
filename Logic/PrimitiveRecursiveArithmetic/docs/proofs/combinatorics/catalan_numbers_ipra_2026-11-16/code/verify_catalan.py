#!/usr/bin/env python3
"""Independent exact checks for the Catalan/iPRA research packet.

This program is a transcription checker, not a proof assistant.  All core
identity tests use Python integers or fractions.  Floating-point calculations
are isolated under an explicitly diagnostic key.
"""
from __future__ import annotations

import json
import math
import sys
from decimal import Decimal, localcontext
from dataclasses import dataclass, asdict
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Callable, Iterable

sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification" / "certificate.json"
SNAPSHOT = "00bbe871268c453903499fb6afe07519e87d9631"


def choose(n: int, k: int) -> int:
    if k < 0 or k > n or n < 0:
        return 0
    return math.comb(n, k)


def gchoose(n: int, k: int) -> Fraction:
    """Generalized integer-upper binomial coefficient."""
    if k < 0:
        return Fraction(0)
    ans = Fraction(1)
    for j in range(k):
        ans *= Fraction(n - j, j + 1)
    return ans


def cat(n: int) -> int:
    return choose(2 * n, n) // (n + 1)


def cat_diff(n: int) -> int:
    return choose(2 * n, n) - choose(2 * n, n + 1)


def odd_double_factorial(n: int) -> int:
    # n is expected odd; (-1)!! = 1.
    ans = 1
    for j in range(1, n + 1, 2):
        ans *= j
    return ans


def vp_int(x: int, p: int) -> int:
    if x == 0:
        raise ValueError("v_p(0) is not used")
    e = 0
    while x % p == 0:
        x //= p
        e += 1
    return e


def digits_lsf(n: int, base: int) -> list[int]:
    if n == 0:
        return [0]
    out: list[int] = []
    while n:
        out.append(n % base)
        n //= base
    return out


def digit_sum(n: int, base: int) -> int:
    return sum(digits_lsf(n, base))


def primes_upto(n: int) -> list[int]:
    ps: list[int] = []
    for x in range(2, n + 1):
        if all(x % p for p in ps if p * p <= x):
            ps.append(x)
    return ps


def catalan_digit_automaton(n: int, p: int) -> int:
    """Odd-prime automaton in the report, scanning digits of n+1 LSF first."""
    if p == 2:
        return digit_sum(n + 1, 2) - 1
    ds = digits_lsf(n + 1, p)
    t = 0
    while t < len(ds) and ds[t] == 0:
        t += 1
    if t == len(ds):
        return 0
    if t == 0:
        carry = ds[t] >= (p + 3) // 2
    else:
        carry = ds[t] >= (p + 1) // 2
    total = int(carry)
    for d in ds[t + 1 :]:
        carry = d >= (p + 1) // 2 or (d == (p - 1) // 2 and carry)
        total += int(carry)
    return total


def bareiss_det(a: list[list[int]]) -> int:
    """Fraction-free exact determinant."""
    n = len(a)
    if n == 0:
        return 1
    m = [row[:] for row in a]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if m[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if m[i][k] != 0), None)
            if pivot is None:
                return 0
            m[k], m[pivot] = m[pivot], m[k]
            sign = -sign
        pivot_val = m[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = m[i][j] * pivot_val - m[i][k] * m[k][j]
                if k:
                    assert num % prev == 0
                    num //= prev
                m[i][j] = num
        prev = pivot_val
        for i in range(k + 1, n):
            m[i][k] = 0
    return sign * m[n - 1][n - 1]


def even_ballot(r: int, k: int) -> int:
    return choose(2 * r, r - k) - choose(2 * r, r - k - 1)


def odd_ballot(r: int, k: int) -> int:
    return choose(2 * r + 1, r - k) - choose(2 * r + 1, r - k - 1)


def convolve(a: list[int], b: list[int], nmax: int) -> list[int]:
    out = [0] * (nmax + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= nmax:
                out[i + j] += x * y
    return out


def kfold_catalan(k: int, nmax: int) -> list[int]:
    ans = [1] + [0] * nmax
    base = [cat(n) for n in range(nmax + 1)]
    for _ in range(k):
        ans = convolve(ans, base, nmax)
    return ans


def fuss(p: int, k: int) -> int:
    return choose(p * k, k) // ((p - 1) * k + 1)


def power_series_power(base: list[int], p: int, nmax: int) -> list[int]:
    ans = [1] + [0] * nmax
    for _ in range(p):
        ans = convolve(ans, base, nmax)
    return ans


def dpq(p: int, q: int, k: int) -> Fraction:
    if k == 0:
        return Fraction(1 if q == 0 else 0)
    return Fraction(p - q, p * k - q) * gchoose(p * k - q, k - 1)


def super_catalan(m: int, n: int) -> int:
    num = math.factorial(2 * m) * math.factorial(2 * n)
    den = math.factorial(m) * math.factorial(n) * math.factorial(m + n)
    assert num % den == 0
    return num // den


@dataclass
class Check:
    name: str
    cases: int
    details: str


checks: list[Check] = []


def record(name: str, cases: int, details: str) -> None:
    checks.append(Check(name, cases, details))


# Closed forms, product, ratio, and Segner.
count = 0
for n in range(0, 101):
    c = cat(n)
    assert c == cat_diff(n)
    assert (n + 1) * c == choose(2 * n, n)
    assert (2 * n + 1) * c == choose(2 * n + 1, n)
    assert math.factorial(n + 1) * math.factorial(n) * c == math.factorial(2 * n)
    assert math.factorial(n + 1) * c == (2**n) * odd_double_factorial(2 * n - 1)
    assert math.factorial(n + 1) * c == math.prod(4 * j - 2 for j in range(1, n + 1))
    if n >= 1:
        assert n * c == choose(2 * n, n - 1)
    if n < 100:
        assert (n + 2) * cat(n + 1) == 2 * (2 * n + 1) * c
    if n >= 1:
        assert c == sum(cat(k) * cat(n - 1 - k) for k in range(n))
    count += 1
record("closed_forms_ratio_segner", count, "n=0..100; integer-cleared identities")

# Hypergeometric/Narayana sum.
count = 0
for n in range(0, 61):
    if n == 0:
        val = Fraction(1)
    else:
        val = sum(
            Fraction(choose(n, k + 1) * choose(n, k), n)
            for k in range(n)
        )
    assert val == cat(n)
    count += 1
record("terminating_hypergeometric_narayana", count, "n=0..60")

# MathWorld sums (9)--(12).
count = 0
for n in range(0, 61):
    c = cat(n)
    if n >= 1:
        s9 = sum(
            cat(k) * 2 ** (n - 2 * k - 1) * choose(n - 1, 2 * k)
            for k in range((n - 1) // 2 + 1)
        )
        assert s9 == c
        s10_num = sum(cat(n - k - 1) * choose(2 * k + 1, k + 1) for k in range(n))
        assert s10_num == n * c
    s11 = sum((-1) ** k * 2 ** (n - k) * choose(n, k) * choose(k, k // 2) for k in range(n + 1))
    assert s11 == c
    s12 = sum((choose(n, k) - choose(n, k - 1)) ** 2 for k in range(n // 2 + 1))
    assert s12 == c
    count += 1
record("mathworld_sums_9_to_12", count, "n=0..60 (range-correct form for sum 9)")

# Riordan/Catalan binomial inversion.  R_n counts singleton-free
# noncrossing partitions; here it is computed from the exact inverse formula.
count = 0
riordan: list[int] = []
for n in range(0, 101):
    r = sum((-1) ** (n - k) * choose(n, k) * cat(k) for k in range(n + 1))
    assert r >= 0
    riordan.append(r)
    assert sum(choose(n, k) * riordan[k] for k in range(n + 1)) == cat(n)
    count += 1
assert riordan[:16] == [1, 0, 1, 1, 3, 6, 15, 36, 91, 232, 603, 1585, 4213, 11298, 30537, 83097]
record("riordan_binomial_inversion", count, "n=0..100; exact signed inversion and reconstruction")

# Exact boundary telescope and tail square inequality.
count = 0
for N in range(0, 101):
    m = N + 1
    partial = sum(Fraction(cat(n), 4**n) for n in range(N + 1))
    remainder = Fraction(2 * choose(2 * m, m), 4**m)
    assert partial + remainder == 2
    assert remainder * remainder <= Fraction(4, m + 1)
    count += 1
record("boundary_sum_exact_tail", count, "N=0..100; exact Fractions")

# Ballot Gram identities and Hankel determinants.
count = 0
for r in range(0, 15):
    for s in range(0, 15):
        assert sum(even_ballot(r, k) * even_ballot(s, k) for k in range(min(r, s) + 1)) == cat(r + s)
        assert sum(odd_ballot(r, k) * odd_ballot(s, k) for k in range(min(r, s) + 1)) == cat(r + s + 1)
        count += 2
for n in range(1, 10):
    h0 = [[cat(i + j) for j in range(n)] for i in range(n)]
    h1 = [[cat(i + j + 1) for j in range(n)] for i in range(n)]
    h2 = [[cat(i + j + 2) for j in range(n)] for i in range(n)]
    assert bareiss_det(h0) == 1
    assert bareiss_det(h1) == 1
    assert bareiss_det(h2) == n + 1
    M = [[even_ballot(r + 1, k) for k in range(n + 1)] for r in range(n)]
    for deleted in range(n + 1):
        minor = [[row[k] for k in range(n + 1) if k != deleted] for row in M]
        assert bareiss_det(minor) == 1
        count += 1
record("ballot_gram_and_hankel", count, "r,s=0..14; determinants n=1..9; all maximal minors")

# Valuations, parity, and odd-prime digit automaton.
count = 0
for p in primes_upto(47):
    for n in range(0, 301):
        actual = vp_int(cat(n), p) if cat(n) else 0
        formula = (2 * digit_sum(n, p) - digit_sum(2 * n, p)) // (p - 1) - vp_int(n + 1, p)
        assert actual == formula
        assert actual == catalan_digit_automaton(n, p)
        if p == 2:
            assert actual == digit_sum(n + 1, 2) - 1
            assert (actual == 0) == ((n + 1) & n == 0)
        count += 1
record("prime_valuations_and_digit_automata", count, "primes <=47, n=0..300")

# Base-five final-digit criterion on odd Catalan indices.
exceptions: list[int] = []
for k in range(0, 1001):
    N = 1 << k
    ds = digits_lsf(N, 5)
    no_five = ds[0] <= 3 and all(d <= 2 for d in ds[1:])
    if no_five:
        exceptions.append(k)
    assert no_five == (catalan_digit_automaton(N - 1, 5) == 0)
record("base5_odd_catalan_criterion", 1001, f"k=0..1000; exceptions={exceptions}")

# k-fold convolution.
count = 0
for k in range(1, 9):
    vals = kfold_catalan(k, 25)
    for n in range(0, 26):
        rhs = Fraction(k * choose(2 * n + k, n), 2 * n + k)
        assert rhs.denominator == 1
        assert vals[n] == rhs.numerator
        count += 1
record("kfold_convolution", count, "k=1..8, n=0..25")

# Fuss-Catalan recurrence T = 1 + x T^p.
count = 0
for p in range(2, 8):
    vals = [fuss(p, k) for k in range(0, 21)]
    power = power_series_power(vals, p, 19)
    for k in range(1, 20):
        assert vals[k] == power[k - 1]
        count += 1
record("fuss_catalan", count, "p=2..7, k=1..19")

# Generalized Jonah identity and convolution.
count = 0
for p in range(2, 8):
    for q in range(0, p):
        for k in range(1, 13):
            for n in range(p * k, p * k + 4):
                lhs = gchoose(n - q, k - 1)
                rhs = sum(dpq(p, q, i) * gchoose(n - p * i, k - i) for i in range(1, k + 1))
                assert lhs == rhs
                count += 1
        for r in range(1, p - q):
            if not (q < p - r):
                continue
            for k in range(1, 12):
                lhs = dpq(p, q, k)
                rhs = sum(dpq(p, p - r, i) * dpq(p, q + r, j)
                          for i in range(1, k + 1) for j in range(1, k + 1)
                          if i + j == k + 1)
                assert lhs == rhs
                count += 1
record("generalized_jonah_and_convolution", count, "p=2..7; admissible q,r; exact Fractions")

# Super-Catalan integrality and special cases.
count = 0
for m in range(0, 21):
    for n in range(0, 21):
        s = super_catalan(m, n)
        if m == 1:
            assert s == 2 * cat(n)
        if m == n:
            assert s == choose(2 * n, n)
        count += 1
record("super_catalan_integrality", count, "m,n=0..20")

# Coxeter source corrections: standard type-A indexing, weighted deletion, B2.
count = 0
for n in range(1, 101):
    parabolic_sum = sum(cat(i) * cat(n + 1 - i) for i in range(1, n + 1))
    assert 2 * n * cat(n + 1) == (n + 3) * parabolic_sum
    count += 1
# A2 disproves the unweighted standard-Catalan deletion statement.
assert cat(3) == 5 and 2 * cat(2) == 4
count += 1
# B2 positive-root poset: two incomparable minima, then a two-element chain.
comparables = {(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}
root_antichains = 0
for mask in range(1 << 4):
    subset = [i for i in range(4) if mask & (1 << i)]
    if all((min(a, b), max(a, b)) not in comparables for a in subset for b in subset if a < b):
        root_antichains += 1
assert root_antichains == 6
# I_2(4) has reduced lengths 0,1,1,2,2,3,3,4; only the longest
# element needs the noncommutation braid stst=tsts and is not fully commutative.
fully_commutative_B2 = 1 + 2 + 2 + 2
assert fully_commutative_B2 == 7 and fully_commutative_B2 != root_antichains
count += 1
record("coxeter_source_corrections", count,
       "type A n=1..100; A2 unweighted counterexample; B2 has 6 antichains versus 7 fully commutative elements")

# Decimal digit data feasible in this packet.
digit_values: list[int] = []
for m in range(0, 5):
    n = 10**m
    digit_values.append(len(str(cat(n))))
assert digit_values == [1, 5, 57, 598, 6015]
record("decimal_digit_initial_values", 5, f"m=0..4: {digit_values}")

# Diagnostic only: high-precision decimal evaluation of the effective asymptotic error.
max_scaled_error = Decimal(0)
max_at = 0
with localcontext() as ctx:
    ctx.prec = 80
    pi_dec = Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816406286")
    qcentral = Decimal(1)  # binom(2n,n)/4^n, updated from n-1 to n
    for n in range(1, 20001):
        qcentral *= Decimal(2 * n - 1) / Decimal(2 * n)
        if n < 8:
            continue
        nd = Decimal(n)
        r = pi_dec.sqrt() * nd * nd.sqrt() * qcentral / Decimal(n + 1)
        approx = Decimal(1) - Decimal(9) / (Decimal(8) * nd) + Decimal(145) / (Decimal(128) * nd * nd)
        scaled = abs(r - approx) * nd**3
        if scaled > max_scaled_error:
            max_scaled_error = scaled
            max_at = n
assert max_scaled_error < Decimal(2)
record("asymptotic_decimal_diagnostic", 19993,
       f"n=8..20000; max n^3 error={max_scaled_error} at n={max_at}; theorem bound=2")

certificate = {
    "status": "PASS",
    "generated_for": "catalan_numbers_ipra_2026-11-16",
    "repository_snapshot": SNAPSHOT,
    "python": sys.version.split()[0],
    "checks": [asdict(c) for c in checks],
    "total_assertion_families": len(checks),
    "total_reported_cases": sum(c.cases for c in checks),
    "notes": [
        "All non-diagnostic checks use exact integers or fractions.",
        "The floating asymptotic check is a transcription diagnostic, not part of the proof.",
        "The Lean blueprint is not compiled in this environment because Lean is unavailable.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
print(json.dumps(certificate, indent=2))
