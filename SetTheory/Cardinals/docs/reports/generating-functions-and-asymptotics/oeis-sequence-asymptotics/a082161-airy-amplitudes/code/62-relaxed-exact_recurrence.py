#!/usr/bin/env python3
"""Exact rational recurrence, gauge, and half-line Catalan kernel checks."""
if not __debug__:
    raise RuntimeError("Run with assertions enabled; do not use python -O")

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path


def check(size=14, gauge_max=40):
    # r[n,m]=r[n,m-1]+(m+1)r[n-1,m], with the zero extension m>n.
    triangle = [[0] * (size + 1) for _ in range(size + 1)]
    for n in range(size + 1):
        triangle[n][0] = 1
        for m in range(1, n + 1):
            triangle[n][m] = triangle[n][m-1] + (m+1) * triangle[n-1][m]
    d, diagonal = [Fraction(1)], [1]
    count = 0
    for N in range(1, 2*size+1):
        old = d + [Fraction(0)] * 3
        d = [Fraction(0)] * (N+2)
        for j in range(N % 2, N+1, 2):
            d[j] = old[j+1]
            if j:
                d[j] += Fraction(N-j+2, N+j) * old[j-1]
            n, m = (N+j)//2, (N-j)//2
            if n <= size:
                assert d[j] * math.factorial(n) == triangle[n][m]
                count += 1
        if N % 2 == 0:
            value = d[0] * math.factorial(N//2)
            assert value.denominator == 1
            diagonal.append(int(value))
    assert diagonal[:10] == [1,1,3,16,127,1363,18628,311250,6173791,142190703]

    def D2(N, j):
        return Fraction(math.factorial(N+1)*math.factorial(N),
                        math.factorial(N-j+1)*math.factorial(N+j))

    gauge_count = 0
    for N in range(1, gauge_max+1):
        for j in range(1, N+2):
            assert D2(N,j)/D2(N,j-1) == Fraction(N-j+2,N+j)
            gauge_count += 1
        for j in range(N+1):
            assert D2(N-1,j)/D2(N,j) == 1-Fraction(j*(j-1),N*(N+1))
            gauge_count += 1

    # Row of powers of the half-line adjacency, with the Dirichlet wall at -1.
    row = [1]
    catalan_checks = []
    for ell in range(25):
        norm2 = sum(v*v for v in row)
        expected = math.comb(2*ell,ell)//(ell+1)
        assert norm2 == expected
        catalan_checks.append({"ell": ell, "squared_row_norm": norm2})
        extended = row + [0,0]
        row = [(extended[j-1] if j else 0)+extended[j+1]
               for j in range(len(row)+1)]
    return {"passed": True, "arithmetic": "Python integers and fractions.Fraction; exact",
            "sequence_first_15": diagonal, "triangle_comparisons": count,
            "gauge_max_N": gauge_max, "gauge_comparisons": gauge_count,
            "catalan_kernel_checks": catalan_checks,
            "limitation": "Finite exact identities only; not a proof of asymptotic remainder bounds"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent / "output" / "exact_recurrence.json")
    args = parser.parse_args()
    result = check()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
