#!/usr/bin/env python3
"""Reproduce all reported exact checks; stop immediately on a discrepancy."""
from __future__ import annotations
import json
import platform
import time
from pathlib import Path
from math import comb
import sympy
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ
from hankel import (source_hankel, parity_formula, auxiliary_corner,
                    auxiliary_closed, alternant_numerator, stable_coefficient,
                    normalized_source, schur_candidate, cigler_moment)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: the verification suite uses assertions.")
    started = time.monotonic()
    out = Path(__file__).resolve().parents[1] / 'data'
    out.mkdir(exist_ok=True)
    counts = {}
    R, t = ring('t', ZZ)

    # Independent integer evaluations, including exceptional t=0,+/-1.
    cases = 0
    for tv in [-3, -2, -1, 0, 1, 2, 3, 5]:
        for k in range(1, 13):
            for n in range(13):
                p = parity_formula(k, n, tv)
                q = n * (n - 1) // 2
                assert source_hankel(k, n, tv) == (-1) ** (k * q) * tv ** q * p
                cases += 1
    counts['source_vs_parity_integer'] = cases
    print(f'PASS: {cases} source/parity integer evaluations', flush=True)

    cases = 0
    for tv in [-3, -2, 0, 2, 3, 5]:
        for a in range(8):
            for m in range(9):
                for eps in (0, 1):
                    assert auxiliary_corner(a, m, tv, eps) == auxiliary_closed(a, m, tv, eps)
                    cases += 1
    counts['corner_vs_alternant_integer'] = cases
    print(f'PASS: {cases} corner/alternant integer evaluations', flush=True)

    # Polynomial identities are exact in ZZ[t], not numerical interpolation.
    cases = 0
    samples = []
    for k in range(1, 11):
        for n in range(9):
            p = normalized_source(k, n, t)
            assert p == parity_formula(k, n, t)
            assert p == parity_formula(k, n, t, auxiliary_closed)
            degree = (k - 1) * n
            coefficients = [int(p.get((j,), 0)) for j in range(degree + 1)]
            assert p.degree() == degree
            assert coefficients == coefficients[::-1]
            assert all(c > 0 for c in coefficients)
            for j in range(n + 1):
                assert p.get((j,), 0) == stable_coefficient(k, j)
            if k >= 2:
                a = k // 2
                assert stable_coefficient(k, n + 1) - p.get((n + 1,), 0) == comb(n + a, a - 1)
            cases += 1
            if k <= 8 and n <= 5:
                samples.append({'k': k, 'n': n, 'coefficients_low_to_high': coefficients})
    counts['three_way_polynomial_identities_and_main_theorem'] = cases
    print(f'PASS: {cases} full polynomial checks and all main-theorem assertions', flush=True)

    cases = 0
    for a in range(1, 7):
        for m in range(7):
            for eps in (0, 1):
                numerator = alternant_numerator(a, m, t, 1 - eps)
                r = 2 * m + 2 - eps
                assert numerator.get((0,), 0) == 1
                assert all(not numerator.get((j,), 0) for j in range(1, r))
                assert numerator.get((r,), 0) == -comb(a + r - 1, a - 1)
                cases += 1
    counts['auxiliary_first_defect_polynomial'] = cases
    print(f'PASS: {cases} exact auxiliary numerator/first-defect checks', flush=True)

    # Stronger Schur identity is explicitly experimental, not a proof dependency.
    cases = 0
    for tv in [-3, -2, -1, 0, 1, 2, 3, 5]:
        for k in range(1, 13):
            for n in range(13):
                assert parity_formula(k, n, tv, auxiliary_closed) == schur_candidate(k, n, tv)
                cases += 1
    counts['EXPERIMENTAL_schur_evaluations'] = cases
    print(f'PASS: {cases} experimental Schur evaluations (NOT an all-index proof)', flush=True)

    result = {
        'status': 'all checks passed',
        'arithmetic': 'exact integers and exact ZZ[t] polynomials; no floating point',
        'python': platform.python_version(), 'sympy': sympy.__version__,
        'ranges': {
            'source_integer': '1<=k<=12, 0<=n<=12; t=-3,-2,-1,0,1,2,3,5',
            'aux_integer': '0<=a<=7, 0<=m<=8; eps=0,1; t=-3,-2,0,2,3,5',
            'symbolic': '1<=k<=10, 0<=n<=8',
            'aux_symbolic_defect': '1<=a<=6, 0<=m<=6; eps=0,1',
            'experimental_schur': 'same k,n,t range as source_integer'},
        'counts': counts, 'elapsed_seconds': round(time.monotonic() - started, 3),
        'scope': 'Finite regression tests supplement, but do not replace, the article proof.'}
    (out / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    (out / 'sample_polynomials.json').write_text(json.dumps(samples, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
