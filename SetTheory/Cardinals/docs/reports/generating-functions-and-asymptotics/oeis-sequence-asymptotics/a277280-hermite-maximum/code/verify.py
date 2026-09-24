"""Independent finite checks; mathematical proofs are in article.tex.

Run from the archive root: python code/verify.py
Optional full published b-file comparison:
    python code/verify.py --oeis-file path/to/b277280.txt
The complete OEIS b-file was not downloaded in the supplied verification.
"""
from __future__ import annotations
import argparse
import json
from math import factorial
from pathlib import Path
from random import Random
import sys
import time
from a277280 import a277280, maximizing_exponent, iter_terms, ratio_fraction

PREFIX = [1,2,4,8,16,120,720,3360,13440,48384,302400,2217600,
          13305600,69189120,322882560,2421619200,19372953600,
          131736084480,790416506880,4290832465920,40226554368000,
          337903056691200,2477955749068800,16283709208166400,
          113985964457164800]


def check_mode_neighbors(n: int) -> None:
    d = maximizing_exponent(n)
    assert 0 <= d <= n and (n-d) % 4 == 0
    if d + 4 <= n:
        assert d*d + 7*d + 7 > 2*n
    if d >= 4:
        z = d - 4
        assert z*z + 7*z + 7 < 2*n


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--oeis-file", type=Path)
    args = parser.parse_args()
    start = time.perf_counter()
    checks = {}
    assert [a277280(n) for n in range(len(PREFIX))] == PREFIX
    checks["published_OEIS_prefix"] = "25/25 terms, n=0..24"

    # Independently construct H_n via H_(n+1)=2*x*H_n-2*n*H_(n-1).
    previous, current = [1], [0, 2]
    assert max(previous) == a277280(0)
    for n in range(1, 301):
        assert max(current) == a277280(n)
        d = maximizing_exponent(n)
        assert current[d] == max(current)
        assert sum(c == max(current) for c in current) == 1
        nxt = [0] + [2*c for c in current]
        for j, coefficient in enumerate(previous):
            nxt[j] -= 2*n*coefficient
        previous, current = current, nxt
    checks["independent_polynomial_recurrence"] = "n=0..300"

    # Enumerate all positive coefficients by exact ratios, not mode logic.
    for n in range(801):
        c, d, best, best_d = 1 << n, n, 1 << n, n
        while d >= 4:
            m = (n-d)//2
            numerator = c*d*(d-1)*(d-2)*(d-3)
            denominator = 16*(m+1)*(m+2)
            c, remainder = divmod(numerator, denominator)
            assert remainder == 0
            d -= 4
            if c > best:
                best, best_d = c, d
        assert (best, best_d) == (a277280(n), maximizing_exponent(n))
    checks["exhaustive_positive_coefficient_scan"] = "n=0..800"

    for n, d, value in iter_terms(1000):
        assert value == a277280(n)
        assert d == maximizing_exponent(n)
        numerator, denominator = ratio_fraction(n)
        assert value*numerator == a277280(n+1)*denominator
    checks["streaming_and_ratio_formulas"] = "n=0..1000"

    for n in range(100001):
        check_mode_neighbors(n)
    rng = Random(277280)
    for _ in range(500):
        n = rng.randrange(10**100)
        check_mode_neighbors(n)
        e = maximizing_exponent(n+1)-maximizing_exponent(n)
        assert e in (1,-3)
    checks["exact_neighbor_inequalities"] = "n=0..100000 and 500 seeded random n<10^100"

    for n in range(1000):
        for d in range(n % 4, max(n-3,0), 4):
            lhs = (d+1)*(d+2)*(d+3)*(d+4)-4*(n-d)*(n-d-2)
            rhs = (d*d+7*d+7-2*n)*(d*d+3*d+3+2*n)+3
            assert lhs == rhs
    checks["quartic_factorization"] = "all legal adjacent positive pairs for n<1000"

    if args.oeis_file:
        pairs = []
        for line in args.oeis_file.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith('#'):
                n_text, value_text = line.split()[:2]
                pairs.append((int(n_text), int(value_text)))
        for n, value in pairs:
            assert a277280(n) == value
        checks["optional_external_b_file"] = f"{len(pairs)} terms verified"
    else:
        checks["optional_external_b_file"] = "not supplied; not checked"

    # Mathematical source of bounds: DLMF 5.11(ii). These numerical
    # comparisons are diagnostics, not directed-rounding certificates.
    try:
        import mpmath as mp
        from a277280 import log_values, stirling_log_enclosure
        mp.mp.dps = 90
        for n in [5, 10, 100, 1000, 10000, 10**6, 10**8, 10**12]:
            la, _, _ = log_values(n, 90)
            lo, hi = stirling_log_enclosure(n, 90)
            assert lo < la < hi
        checks["numerical_Stirling_enclosures"] = "8 selected indices through 10^12, 90 requested decimal digits"
    except ImportError:
        checks["numerical_Stirling_enclosures"] = "skipped: mpmath not installed"

    result = {"status": "PASS", "checks": checks,
              "python": sys.version, "elapsed_seconds": round(time.perf_counter()-start, 3)}
    out = Path(__file__).resolve().parents[1]/"data"/"verification.json"
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
