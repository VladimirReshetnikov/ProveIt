#!/usr/bin/env python3
"""Reproduce the centered 3-cube identities and matroid counts.

Uses exact integer/Fraction arithmetic for cube correlations, the centered
expansion, coloop cancellation, and face Cauchy--Schwarz identities. Uses
complex floating-point Fourier transforms only for checking the displayed
Fourier formulas. This is a reproducibility check, not a formal proof.

Run:
    python verification/verify_cubes.py
Optional:
    python verification/verify_cubes.py --output path/to/summary.json
Dependency: numpy. No network or external files are used.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random

import numpy as np

VERTICES = list(product((0, 1), repeat=3))
COLUMNS = [(1, *v) for v in VERTICES]
EXPECTED_COUNTS = [1, 0, 0, 0, 12, 8, 28, 8, 1]


def rank_of_mask(mask: int, p: int | None = None) -> int:
    inds = [j for j in range(8) if (mask >> j) & 1]
    a = [[COLUMNS[j][row] for j in inds] for row in range(4)]
    if p is None:
        a = [[Fraction(x) for x in row] for row in a]
    rank = 0
    for c in range(len(inds)):
        pivot = next((j for j in range(rank, 4) if a[j][c] != 0), None)
        if pivot is None:
            continue
        a[pivot], a[rank] = a[rank], a[pivot]
        inv = 1 / a[rank][c] if p is None else pow(int(a[rank][c]), -1, p)
        a[rank] = [x * inv for x in a[rank]]
        if p is not None:
            a[rank] = [int(x) % p for x in a[rank]]
        for row in range(4):
            if row == rank:
                continue
            factor = a[row][c]
            a[row] = [x - factor * y for x, y in zip(a[row], a[rank])]
            if p is not None:
                a[row] = [int(x) % p for x in a[row]]
        rank += 1
        if rank == 4:
            break
    return rank


def matroid_data(p: int | None = None) -> tuple[list[int], list[bool]]:
    ranks = [rank_of_mask(mask, p) for mask in range(256)]
    coloopless = [all(ranks[mask ^ (1 << j)] == ranks[mask]
                     for j in range(8) if (mask >> j) & 1)
                 for mask in range(256)]
    counts = [sum(coloopless[mask] for mask in range(256)
                  if mask.bit_count() == s) for s in range(9)]
    return counts, coloopless


def compact_fraction(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def exact_correlations(values: list[int], denom: int) -> list[Fraction]:
    p = len(values)
    x, h1, h2, h3 = np.indices((p, p, p, p), dtype=np.int64)
    vals = np.asarray(values, dtype=np.int64)
    cubes = np.stack([vals[(x + v[0]*h1 + v[1]*h2 + v[2]*h3) % p]
                      for v in VERTICES], axis=-1).reshape(-1, 8)
    corr = [Fraction(1)]
    # Bound avoids silent numpy integer overflow in this deterministic check.
    assert p**4 * max(1, max(abs(v) for v in values))**8 < 2**63
    for mask in range(1, 256):
        inds = [j for j in range(8) if (mask >> j) & 1]
        numerator = int(np.prod(cubes[:, inds], axis=1, dtype=np.int64)
                        .sum(dtype=np.int64))
        corr.append(Fraction(numerator, p**4 * denom**len(inds)))
    return corr


def mask_of(vertices: list[tuple[int, int, int]]) -> int:
    return sum(1 << VERTICES.index(v) for v in vertices)


def check_case(p: int, raw: list[int], coloopless: list[bool]) -> dict:
    assert len(raw) == p and sum(raw) == 0 and any(raw)
    scale = max(abs(x) for x in raw)
    denom = 2 * scale
    f = np.asarray(raw, dtype=float) / denom
    corr = exact_correlations(raw, denom)
    assert all(corr[mask] == 0 for mask in range(256) if not coloopless[mask])

    rho4 = corr[mask_of([(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1)])]
    t5 = corr[mask_of([(0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 1)])]
    b1 = corr[255 ^ (1 << 0) ^ (1 << 1)]
    b2 = corr[255 ^ (1 << 0) ^ (1 << 3)]
    b3 = corr[255 ^ (1 << 0) ^ (1 << 7)]
    t7 = corr[254]
    eta8 = corr[255]
    assert rho4 >= 0 and b1 >= 0 and eta8 >= 0

    for mask in range(256):
        if not coloopless[mask]:
            continue
        size = mask.bit_count()
        if size == 4:
            assert corr[mask] == rho4
        elif size == 5:
            assert corr[mask] == t5
        elif size == 6:
            missing = [VERTICES[j] for j in range(8) if not ((mask >> j) & 1)]
            distance = sum(a != b for a, b in zip(*missing))
            assert corr[mask] == {1: b1, 2: b2, 3: b3}[distance]
        elif size == 7:
            assert corr[mask] == t7

    delta = Fraction(1, 2)
    expanded = sum(delta**(8-mask.bit_count()) * corr[mask]
                   for mask in range(256))
    claimed = (delta**8 + 12*delta**4*rho4 + 8*delta**3*t5
               + delta**2*(12*b1 + 12*b2 + 4*b3) + 8*delta*t7 + eta8)
    weighted = exact_correlations([v + scale for v in raw], denom)[255]
    assert expanded == claimed == weighted

    # Physical-space identities, exactly: B1=E C(h)^3,
    # E A(a,b)^2=B1, E B(a,b)^2=eta8.
    c_num = [sum(raw[x]*raw[(x+h) % p] for x in range(p)) for h in range(p)]
    assert Fraction(sum(c**3 for c in c_num), p**4*denom**6) == b1
    a_sq = b_sq = 0
    for a in range(p):
        for b in range(p):
            an = sum(raw[(x+a) % p]*raw[(x+b) % p]*raw[(x+a+b) % p]
                     for x in range(p))
            bn = sum(raw[x]*raw[(x+a) % p]*raw[(x+b) % p]*raw[(x+a+b) % p]
                     for x in range(p))
            a_sq += an**2
            b_sq += bn**2
    assert Fraction(a_sq, p**4*denom**6) == b1
    assert Fraction(b_sq, p**4*denom**8) == eta8
    assert t7**2 <= b1*eta8
    sigma2 = Fraction(sum(v*v for v in raw), p*denom**2)
    assert b1 <= sigma2*rho4
    assert b1 <= sigma2*rho4 - rho4**2/sigma2
    assert b2**2 <= b1**2 and b3**2 <= b1**2
    # B1 <= eta^6 is equivalent to B1^4 <= (eta^8)^3.
    assert b1**4 <= eta8**3

    a = np.fft.fft(f)/p
    r = np.arange(p)
    rr, ss = np.indices((p, p))
    f_rho4 = np.sum(abs(a)**4)
    f_t5 = np.sum(abs(a)**2 * a**2 * np.conj(a[(2*r) % p]))
    f_b1 = np.sum(abs(a[rr])**2 * abs(a[ss])**2 * abs(a[(rr+ss) % p])**2)
    f_b2 = np.sum(abs(a[rr])**2 * a[ss]**2 * a[(rr-ss) % p]
                  * np.conj(a[(rr+ss) % p]))
    f_b3 = np.sum(a[rr]**2 * a[ss]**2 * a[(-rr-ss) % p]**2)
    uu, vv, ww = np.indices((p, p, p))
    f_t7 = np.sum(a[(vv+ww) % p] * a[(uu+ww) % p]
                  * a[(-uu-vv-2*ww) % p] * a[(-uu-vv-ww) % p]
                  * a[uu] * a[vv] * a[ww])
    fourier_pairs = [(f_rho4, rho4), (f_t5, t5), (f_b1, b1),
                     (f_b2, b2), (f_b3, b3), (f_t7, t7)]
    max_error = max(float(abs(z-complex(float(exact)))) for z, exact in fourier_pairs)
    assert max_error < 5e-13, max_error
    zeta = float(np.max(abs(a)))
    assert abs(float(t5)) <= zeta*float(rho4) + 5e-13

    return {
        "p": p,
        "integer_values": raw,
        "denominator": denom,
        "exact_centered_expansion": True,
        "exact_coloop_cancellation": True,
        "exact_orbit_correlations": True,
        "exact_face_square_identities": True,
        "exact_Cauchy_Schwarz_bounds": True,
        "maximum_Fourier_error": max_error,
        "rho4": compact_fraction(rho4),
        "T5": compact_fraction(t5),
        "B1": compact_fraction(b1),
        "B2": compact_fraction(b2),
        "B3": compact_fraction(b3),
        "T7": compact_fraction(t7),
        "eta8": compact_fraction(eta8),
    }


def check_sign_examples() -> dict:
    p = 17
    b = 0.6
    x = np.arange(p)
    g1 = np.cos(2*np.pi*x/p)-b*np.cos(4*np.pi*x/p)
    g2 = np.cos(2*np.pi*x/p)+b*np.sin(4*np.pi*x/p)
    a1, a2 = np.fft.fft(g1)/p, np.fft.fft(g2)/p
    r = np.arange(p)
    rr, ss = np.indices((p, p))
    t5 = np.sum(abs(a1)**2*a1**2*np.conj(a1[2*r % p]))
    b1 = np.sum(abs(a2[rr])**2*abs(a2[ss])**2*abs(a2[(rr+ss) % p])**2)
    b3 = np.sum(a2[rr]**2*a2[ss]**2*a2[(-rr-ss) % p]**2)
    assert abs(t5 + b/16) < 1e-12
    assert abs(b1 - 3*b*b/32) < 1e-12
    assert abs(b3 + 3*b*b/32) < 1e-12
    return {"p": p, "b": b, "T5": float(t5.real), "B1": float(b1.real),
            "B3": float(b3.real), "negative_T5_verified": True,
            "sharp_abs_B3_le_B1_verified": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("cube_verification_summary.json"))
    args = parser.parse_args()
    q_counts, q_coloopless = matroid_data()
    assert q_counts == EXPECTED_COUNTS
    rank_checks = {"Q": q_counts}
    for p in [3, 5, 7, 11, 13]:
        counts, coloopless = matroid_data(p)
        assert counts == EXPECTED_COUNTS
        assert coloopless == q_coloopless
        rank_checks[str(p)] = counts
    rng = random.Random(20261006)
    cases = []
    for p in [3, 5, 7, 11, 13]:
        for index in range(3):
            prefix = [rng.randint(-2, 2) for _ in range(p-1)]
            raw = prefix + [-sum(prefix)]
            if not any(raw):
                raw[0], raw[1] = 1, -1
            cases.append(check_case(p, raw, q_coloopless))
    signs = check_sign_examples()
    summary = {
        "status": "passed",
        "scope": "Exact finite checks and floating-point Fourier checks; not a formal proof",
        "numpy_version": np.__version__,
        "matroid_counts_by_field": rank_checks,
        "all_256_subsets_checked_per_case": True,
        "number_of_function_cases": len(cases),
        "maximum_Fourier_error": max(c["maximum_Fourier_error"] for c in cases),
        "sign_examples": signs,
        "function_cases": cases,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "fields": list(rank_checks),
                      "function_cases": len(cases),
                      "maximum_Fourier_error": summary["maximum_Fourier_error"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
