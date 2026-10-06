"""Reproducible structural certificates and high-precision diagnostic tests.

Run from this directory: python verify.py --output ../verification.json
The exact tests do not depend on floating-point arithmetic. Fourier tests use
mpmath (80 decimal digits); they are numerical checks, not formal proofs.
"""
from __future__ import annotations
import argparse
import json
import random
from fractions import Fraction as F
from math import prod
from pathlib import Path
import mpmath as mp
from phase_partitions import (single_partition, simultaneous_partition,
                             check_partition, water_fill, capped_partition)


def safe_fraction(x: mp.mpf) -> F:
    denominator = 10**12
    numerator = int(mp.floor(x * denominator)) - 2
    if numerator <= 0:
        raise ValueError("Test width too small for chosen diagnostic denominator.")
    return F(numerator, denominator)


def structural_tests() -> dict:
    count = 0
    nontrivial = 0
    capped = 0
    for n in range(1, 42):
        for modulus in range(2, 12):
            for a in range(modulus):
                for eps in [F(1, 20), F(1, 7), F(1, 4), F(1, 2), F(1)]:
                    L, cells = single_partition(n, F(a, modulus), eps)
                    check_partition(n, L, cells, [F(a, modulus)], [eps])
                    count += 1
                    nontrivial += L > 1
                    if eps*n >= 1:
                        K, capped_cells = capped_partition(n, F(a, modulus), eps)
                        check_partition(n, K, capped_cells, [F(a, modulus)], [eps])
                        assert all(9*p.length*p.length >= eps*n and
                                   p.length*p.length <= eps*n for p in capped_cells)
                        capped += 1
    rng = random.Random(20261006)
    multi = 0
    multi_nontrivial = 0
    for dimension in range(1, 5):
        for _ in range(80):
            n = rng.randrange(25, 1501)
            slopes = [F(rng.randrange(0, 101), rng.randrange(2, 102))
                      for _ in range(dimension)]
            widths = [F(rng.randrange(1, 5), 10) for _ in range(dimension)]
            L, cells = simultaneous_partition(n, slopes, widths)
            check_partition(n, L, cells, slopes, widths)
            multi += 1
            multi_nontrivial += L > 1
    for _ in range(200):
        ws = [F(rng.randrange(1, 100), 101) for _ in range(rng.randrange(1, 8))]
        budget = sum(ws, F(0)) * F(rng.randrange(1, 25), 100)
        widths = water_fill(ws, budget)
        assert all(0 < x <= F(1, 4) for x in widths)
        assert sum(w*x for w, x in zip(ws, widths)) <= budget
        free = [w*x for w, x in zip(ws, widths) if x < F(1, 4)]
        assert not free or len(set(free)) == 1
        uniform = min(F(1, 4), budget / sum(ws))
        assert prod(widths) >= uniform ** len(ws)
    return {"single_phase_exact_cases": count,
            "sharp_capped_exact_cases": capped,
            "single_phase_cases_with_L_gt_1": nontrivial,
            "simultaneous_exact_cases": multi,
            "simultaneous_cases_with_L_gt_1": multi_nontrivial,
            "water_filling_exact_cases": 200}


def fourier_tests() -> dict:
    mp.mp.dps = 80
    rng = random.Random(31062026)
    correlation_cases = 0
    spectral_cases = 0
    nontrivial_spectral = 0
    minimum_correlation_margin = mp.inf
    minimum_spectral_margin = mp.inf
    for n in [31, 64, 127, 251, 509, 1024]:
        for trial in range(5):
            # Structured and mixed examples, always neither empty nor full.
            size = max(2, int(n * (trial + 1) / 12))
            A = set(range(size)) if trial % 2 == 0 else set(rng.sample(range(n), size))
            delta = mp.mpf(len(A)) / n
            v = delta * (1 - delta)
            root = mp.exp(2j * mp.pi / n)
            characters = {r: [root**((r*x) % n) for x in range(n)]
                          for r in [1, 2, 3]}
            coefficients = {r: sum(mp.conj(characters[r][x]) for x in A) / n
                            for r in characters}
            for r in [1, 2]:
                alpha = abs(coefficients[r])
                if alpha < mp.mpf('1e-8'):
                    continue
                eps = safe_fraction(alpha / (4 * mp.pi * v))
                L, cells = single_partition(n, F(r, n), eps)
                check_partition(n, L, cells, [F(r, n)], [eps])
                gs = [(mp.mpf(sum(x in A for x in p.points())) / p.length - delta)
                      for p in cells]
                s = alpha / 4
                eta = delta * s / (delta - s)
                margin = max(gs) - eta
                assert margin >= -mp.mpf('1e-65')
                union = sum(p.length for p, g in zip(cells, gs) if g >= eta/2) / mp.mpf(n)
                bound = s / (2 * (1 - delta - eta/2))
                assert union >= bound - mp.mpf('1e-65')
                minimum_correlation_margin = min(minimum_correlation_margin, margin)
                correlation_cases += 1
            for R in [[1], [1, 2], [1, 2, 3]]:
                E = sum(abs(coefficients[r])**2 for r in R)
                Sigma = sum(abs(coefficients[r]) for r in R)
                eps = safe_fraction(E / (4 * mp.pi * v * Sigma))
                L, cells = simultaneous_partition(n, [F(r, n) for r in R], [eps]*len(R))
                check_partition(n, L, cells, [F(r, n) for r in R], [eps]*len(R))
                gs = [(mp.mpf(sum(x in A for x in p.points())) / p.length - delta)
                      for p in cells]
                V = sum(mp.mpf(p.length)*g*g for p, g in zip(cells, gs)) / n
                boundV = E / (1 + mp.sqrt(1 - E/v))**2
                margin = V - boundV
                assert margin >= -mp.mpf('1e-65')
                assert max(gs) >= boundV/delta - mp.mpf('1e-65')
                minimum_spectral_margin = min(minimum_spectral_margin, margin)
                spectral_cases += 1
                nontrivial_spectral += L > 1
    # Larger, genuinely non-singleton multi-frequency tests. The set is a
    # modular pullback of an interval, so coefficients are evaluated by an
    # independent geometric-series formula, without summing 32768 roots.
    multi_nontrivial = 0
    for n in [8192, 32768]:
        r = (int(n * 0.61803398875) // 2) * 2 + 1
        for frac in [F(1, 8), F(1, 4), F(3, 8)]:
            size = int(n * frac)
            A = {x for x in range(n) if (r*x) % n < size}
            delta = mp.mpf(size)/n
            v = delta*(1-delta)
            cs = []
            for harmonic in [1, 2]:
                z = mp.exp(-2j*mp.pi*harmonic/n)
                cs.append((1-z**size)/(1-z)/n)
            E = sum(abs(c)**2 for c in cs)
            Sigma = sum(abs(c) for c in cs)
            eps = safe_fraction(E/(4*mp.pi*v*Sigma))
            slopes = [F(r, n), F((2*r) % n, n)]
            L, cells = simultaneous_partition(n, slopes, [eps, eps])
            check_partition(n, L, cells, slopes, [eps, eps])
            gs = [(mp.mpf(sum(x in A for x in p.points()))/p.length-delta)
                  for p in cells]
            V = sum(mp.mpf(p.length)*g*g for p,g in zip(cells,gs))/n
            boundV = E/(1+mp.sqrt(1-E/v))**2
            assert V >= boundV - mp.mpf('1e-65')
            assert max(gs) >= boundV/delta - mp.mpf('1e-65')
            spectral_cases += 1
            nontrivial_spectral += L > 1
            multi_nontrivial += L > 1
            minimum_spectral_margin = min(minimum_spectral_margin, V-boundV)
    return {"decimal_digits": mp.mp.dps,
            "multi_frequency_cases_with_L_gt_1": multi_nontrivial,
            "correlation_and_popularity_cases": correlation_cases,
            "spectral_energy_cases": spectral_cases,
            "spectral_cases_with_L_gt_1": nontrivial_spectral,
            "minimum_observed_density_margin": mp.nstr(minimum_correlation_margin, 18),
            "minimum_observed_variance_margin": mp.nstr(minimum_spectral_margin, 18),
            "status": "Numerical diagnostics only; the article supplies proofs."}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('../verification.json'))
    parser.add_argument('--part', choices=['exact', 'fourier', 'all'], default='all')
    args = parser.parse_args()
    result = {"status": "passed",
              "seeds": {"structural": 20261006, "fourier": 31062026},
              "formal_lean_verification": False}
    if args.part in ['exact', 'all']:
        result['exact_structural_tests'] = structural_tests()
    if args.part in ['fourier', 'all']:
        result['fourier_diagnostics'] = fourier_tests()
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
