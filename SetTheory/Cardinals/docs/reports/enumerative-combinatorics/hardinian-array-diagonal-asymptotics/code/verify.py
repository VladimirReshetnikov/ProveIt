#!/usr/bin/env python3
"""Run independent exact checks and write a reproducible JSON audit.

Standard library only.  All assertions are finite checks, not substitutes for
an all-n proof.  Run from any working directory: python code/verify.py
"""
from __future__ import annotations
import json
import platform
import sys
import time
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
from hardinian import (array_count, bareiss, counts, direct_minor_count,
                       matmul, pfaffian, rational_constant,
                       skew_pascal, square_minor_count)

ROOT = Path(__file__).resolve().parents[1]


def rational_det(a: list[list[Fraction]]) -> Fraction:
    b = [list(row) for row in a]
    answer = Fraction(1)
    for i in range(len(b)):
        p = next((j for j in range(i, len(b)) if b[j][i]), None)
        if p is None:
            return Fraction(0)
        if p != i:
            b[i], b[p] = b[p], b[i]
            answer = -answer
        pivot = b[i][i]
        answer *= pivot
        for j in range(i + 1, len(b)):
            q = b[j][i] / pivot
            for k in range(i + 1, len(b)):
                b[j][k] -= q * b[i][k]
    return answer


def moments(q: Fraction, upto: int) -> list[Fraction]:
    # d^k = sum_j S(k,j) d_under_j; sum_d d_under_j q^d
    # = j! q^j / (1-q)^(j+1).
    stirling = [1]
    result = []
    for k in range(upto + 1):
        result.append(sum((Fraction(stirling[j] * factorial(j)) * q ** j
                           / (1 - q) ** (j + 1) for j in range(k + 1)), Fraction(0)))
        stirling = [0] + [stirling[j - 1] + (j * stirling[j] if j <= k else 0)
                          for j in range(1, k + 2)]
    return result


def main() -> None:
    started = time.perf_counter()
    suites = []
    def record(name: str, checks: int) -> None:
        suites.append({"suite": name, "exact_checks": checks, "status": "PASS"})
        print(f"PASS: {name} ({checks} checks)", flush=True)

    num = 0
    for n in range(1, 8):
        h = counts(n, n)
        assert h == counts(n, n, method="generic")
        for r in range(n):
            assert h[r] == array_count(n, r) == direct_minor_count(n, r) == square_minor_count(n, r), (n, r)
            num += 1
    record("Direct arrays vs complementary minors vs squared minors vs both matrix algorithms; n=1..7", num)

    num = 0
    for N in range(1, 13):
        b = [[comb(i, j) if j <= i else 0 for j in range(N)] for i in range(N)]
        jmat = [[int(j > i) - int(j < i) for j in range(N)] for i in range(N)]
        assert skew_pascal(N) == matmul(matmul(b, jmat), list(map(list, zip(*b))))
        num += 1
    record("Skew-Pascal recursion equals B J B^T; N=1..12", num)

    num = 0
    for n in range(1, 15):
        assert counts(n, 7) == counts(n, 7, method="generic")
        assert counts(n, 1)[1] == (4 ** (n - 1) - 1) // 3
        assert counts(n, n, method="generic")[-2:] == [1, 0]
        num += 3
    record("Independent generic Newton coefficients, exact r=1 formula, top degree; n=1..14", num)

    num = 0
    for N in range(0, 8):
        a = skew_pascal(N)
        for r in range(N + 1):
            total = 0
            for inds in combinations(range(N), r):
                m = [[a[i][j] for j in inds] for i in inds]
                if r % 2:
                    for row, i in zip(m, inds):
                        row.append(1 << i)
                    m.append([-(1 << i) for i in inds] + [0])
                total += pfaffian(m) ** 2
            assert total == counts(N + 1, r)[r]
            num += 1
    record("Explicit bordered/unbordered Pfaffian sums; N=0..7", num)

    refs = json.loads((ROOT / "data/oeis_reference_selected.json").read_text())
    for name in ("A253217", "A252998"):
        entry = refs[name]
        for n, val in entry["terms"].items():
            assert counts(int(n), entry["r"])[entry["r"]] == int(val), (name, n)
        record(f"OEIS {name}, independently transcribed reference values", len(entry["terms"]))

    num = 0
    for q in (Fraction(1, 4), Fraction(1, 2), Fraction(2, 3)):
        mu = moments(q, 14)
        for r in range(9):
            d = rational_det([[mu[i + j] for j in range(r)] for i in range(r)])
            F = prod(factorial(j) for j in range(r))
            assert d == q ** (r * (r - 1) // 2) * F ** 2 / (1 - q) ** (r * r)
            num += 1
    record("Geometric Vandermonde partition identity, rational Hankel determinants; r=0..8", num)

    num = 0
    for r in range(21):
        m = r // 2
        if r % 2:
            q = Fraction(2) ** (2 * m * m - 2 * m - 2) * prod(factorial(2*j+1)**2 for j in range(m)) / 3 ** (r*r)
        else:
            q = Fraction(2) ** (2 * m * (m - 2)) * prod(factorial(2*j)**2 for j in range(m)) / 3 ** (r*r)
        assert q == rational_constant(r)
        num += 1
    assert rational_constant(7) == Fraction(2 ** 18 * 5 ** 2, 3 ** 45)
    record("Parity products vs two-step constant recurrence; r=0..20; r=7 correction", num + 1)

    num = 0
    for L in range(1, 18):
        for d in range(L + 1):
            for j in range(L + 1):
                # Rational form of p_(L-d)(j)/p_L(j), no square roots needed.
                f = prod((Fraction(2 * (L - j - h), L - h) for h in range(d)), start=Fraction(1))
                left = Fraction(comb(L-d, j) if j <= L-d else 0, 2 ** (L-d))
                right = Fraction(comb(L, j), 2 ** L) * f
                assert left == right
                num += 1
    record("Exact binomial likelihood-ratio product, including zero tails; L=1..17", num)

    for args in ((0, 2), (-1, 2), (2, -1), (True, 2)):
        try:
            counts(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(f"invalid input accepted: {args}")
    record("Invalid input rejection", 4)

    report = {"status": "PASS", "python": sys.version.split()[0],
              "platform": platform.platform(), "suites": suites,
              "total_exact_checks": sum(s["exact_checks"] for s in suites),
              "elapsed_seconds": round(time.perf_counter() - started, 6),
              "limitation": "Finite verification only. The fixed-r all-n asymptotic proof is in article.tex/article.pdf."}
    path = ROOT / "data/verification_report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"All {report['total_exact_checks']} checks passed; {report['elapsed_seconds']} seconds.")
    print(path)


if __name__ == "__main__":
    main()
