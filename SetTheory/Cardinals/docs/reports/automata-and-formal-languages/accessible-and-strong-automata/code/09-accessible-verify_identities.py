"""Exact replay checks for the accessible-automata expansion research draft.

These finite checks support the derivation; the proof of the asymptotic error
bounds is in accessible-automata.tex.
"""
from functools import lru_cache
from fractions import Fraction
from math import comb, factorial
import json


@lru_cache(None)
def stirling(m, n):
    if m == n == 0:
        return 1
    if n <= 0 or n > m:
        return 0
    return n * stirling(m - 1, n) + stirling(m - 1, n - 1)


def suffix(k, h, r):
    return sum(comb(k * r, j) * h ** (k * r - j) * stirling(j, r)
               for j in range(r, k * r + 1))


def counts(k, nmax):
    labeled = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        labeled[n] = n ** (k * n) - sum(
            comb(n - 1, j - 1) * n ** (k * (n - j)) * labeled[j]
            for j in range(1, n))
    return [0] + [labeled[n] // factorial(n - 1)
                  for n in range(1, nmax + 1)]


def convolve(a, b, degree):
    c = [Fraction(0)] * (degree + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= degree:
                c[i + j] += x * y
    return c


totals = {"first_failure": 0, "finite_difference": 0,
          "uniform_integral": 0, "small_state_h1": 0}
for k in range(2, 7):
    a = counts(k, 15)
    for n in range(1, 16):
        assert stirling(k * n + 1, n) == a[n] + sum(
            a[h] * suffix(k, h, n - h) for h in range(1, n))
        totals["first_failure"] += 1
    for r in range(1, 8):
        degree = (k - 1) * r
        base = [Fraction(1, factorial(j + 1)) for j in range(degree + 1)]
        mgf = [Fraction(1)]
        for _ in range(r):
            mgf = convolve(mgf, base, degree)
        for n in [r + 1, r + 3, r + 11]:
            h = n - r
            exact = suffix(k, h, r)
            fd = sum((-1) ** (r - j) * comb(r, j) * (h + j) ** (k * r)
                     for j in range(r + 1)) // factorial(r)
            assert fd == exact
            totals["finite_difference"] += 1
            normalized = sum(
                (-1) ** j * Fraction(factorial(degree), factorial(degree - j))
                * mgf[j] * Fraction(1, n ** j)
                for j in range(degree + 1))
            assert normalized * comb(k * r, r) * n ** degree == exact
            totals["uniform_integral"] += 1
    for n in range(2, 16):
        assert suffix(k, 1, n - 1) == stirling(k * n - k + 1, n)
        totals["small_state_h1"] += 1

result = {"status": "PASS", "exact_checks": totals,
          "total": sum(totals.values())}
print(json.dumps(result, indent=2))
if __name__ == "__main__":
    from pathlib import Path
    (Path(__file__).resolve().parent.parent / "data" / "identity_verification.json").write_text(
        json.dumps(result, indent=2) + "\n")
