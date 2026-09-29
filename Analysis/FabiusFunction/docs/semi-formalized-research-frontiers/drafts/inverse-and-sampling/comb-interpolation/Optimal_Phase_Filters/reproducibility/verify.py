#!/usr/bin/env python3
"""Independent checks for Complete Superconvergence Phases and Optimal Phase Filters.

Exact checks use fractions.Fraction. The product/series comparisons use mpmath
and are numerical diagnostics, not interval certificates or formal proofs.
Run from any directory: python reproducibility/verify.py
Optional plot: python reproducibility/verify.py --plot
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]


def valuation2(n: int) -> int:
    if n <= 0:
        raise ValueError("valuation2 expects a positive integer")
    return (n & -n).bit_length() - 1


@lru_cache(maxsize=None)
def scaled_d(n: int) -> F:
    if n < 0:
        raise ValueError("negative index")
    if n == 0:
        return F(1)
    return sum((F(comb(n + 1, k)) * scaled_d(k) for k in range(n)), F(0)) / (
        (n + 1) * (2**n - 1)
    )


@lru_cache(maxsize=None)
def base_value(n: int) -> F:
    """Fabius value F(2**(-n)), exact rational arithmetic."""
    if n < 0:
        raise ValueError("negative index")
    return scaled_d(n) / (factorial(n) * 2 ** (n * (n - 1) // 2))


@lru_cache(maxsize=None)
def fabius(x: F) -> F:
    """The bounded Fabius function, exactly at dyadic arguments.

    Uses the standard dyadic finite-Taylor reflection identity. Recursion
    removes the leading nonzero binary digit, so it terminates.
    """
    x = F(x)
    if x <= 0:
        return F(0)
    if x >= 1:
        return F(1)
    if x.denominator & (x.denominator - 1):
        raise ValueError("exact evaluator only accepts dyadic inputs")
    n = 0
    edge = F(1)
    while edge > x:
        n += 1
        edge /= 2
    y = x - edge
    polynomial = sum(
        (F(2 ** (k * (k + 1) // 2), factorial(k)) * base_value(n-k) * y**k
         for k in range(n + 1)), F(0)
    )
    return polynomial - fabius(y)


def up(x: F) -> F:
    x = F(x)
    return F(0) if abs(x) >= 1 else fabius(1 - abs(x))


@lru_cache(maxsize=None)
def moment(n: int) -> F:
    """Moment of Y=(V+Y')/2, V uniform on [-1,1]."""
    if n < 0:
        raise ValueError("negative moment")
    if n == 0:
        return F(1)
    if n % 2:
        return F(0)
    return sum(
        (F(comb(n, k), n-k+1) * moment(k) for k in range(0, n, 2)), F(0)
    ) / (2**n - 1)


def quadrature(M: int, theta: F, degree: int) -> F:
    if M <= 0 or degree < 0:
        raise ValueError("M must be positive and degree nonnegative")
    theta = F(theta) % 1
    # Outside this finite range the support of up gives exact zero.
    return sum(
        (((F(k) + theta) / M)**degree * up((F(k) + theta) / M)
         for k in range(-M - 1, M + 1)), F(0)
    ) / M


def defect(M: int, theta: F, degree: int) -> F:
    return quadrature(M, theta, degree) - moment(degree)


def as_mp(x: F | int) -> mp.mpf:
    x = F(x)
    return mp.mpf(x.numerator) / x.denominator


def fourier_product(x: mp.mpf, factors: int = 120) -> mp.mpf:
    x = mp.mpf(x)
    if not x:
        return mp.mpf(1)
    return mp.fprod(mp.sinpi(x / 2**j) / (mp.pi * x / 2**j)
                    for j in range(factors))


def coefficients(M: int, terms: int = 100) -> tuple[int, mp.mpf, list[mp.mpf]]:
    d = valuation2(M)
    p = d + 1
    a = M // 2**d
    h0 = fourier_product(mp.mpf(a) / 2)
    B = -2 * factorial(p) * h0 / (2 * mp.pi * M)**p
    cs = [fourier_product(mp.mpf(a * k) / 2) / h0 / k**p
          for k in range(1, 2*terms, 2)]
    return p, B, cs


def series_value(theta: F, p: int, B: mp.mpf, cs: list[mp.mpf]) -> mp.mpf:
    x = 2 * mp.pi * as_mp(theta)
    return B * mp.fsum(c * mp.cos(k*x + p*mp.pi/2)
                     for k, c in zip(range(1, 2*len(cs), 2), cs))


def coalesce(atoms: list[tuple[F, F]]) -> dict[F, F]:
    result: dict[F, F] = {}
    for phase, weight in atoms:
        phase = F(phase) % 1
        result[phase] = result.get(phase, F(0)) + F(weight)
    return {phase: weight for phase, weight in result.items() if weight}


def invariant(atoms: list[tuple[F, F]], L: int) -> bool:
    if L < 1:
        raise ValueError("L must be positive")
    current = coalesce(atoms)
    shifted = coalesce([(x + F(1, L), w) for x, w in current.items()])
    return current == shifted


def uniform_atoms(n: int, offset: F = F(0)) -> list[tuple[F, F]]:
    if n < 1:
        raise ValueError("n must be positive")
    return [(offset + F(j, n), F(1, n)) for j in range(n)]


def best_budget(M: F, N: int) -> dict[str, int | None]:
    M = F(M)
    if M <= 0 or N < 1:
        raise ValueError("positive mesh and budget required")
    a, b = M.numerator, M.denominator
    if N < b:
        return {"degree": None, "phases": None}
    s = (N // b).bit_length() - 1
    return {"degree": valuation2(a) + s, "phases": b * 2**s}


def main(make_plot: bool = False) -> None:
    mp.mp.dps = 65
    exact_checks = 0
    assert base_value(1) == F(1, 2)
    assert base_value(2) == F(5, 72)
    assert moment(2) == F(1, 9)
    assert moment(4) == F(19, 675)
    assert defect(1, F(1, 4), 1) == F(13, 72)
    exact_checks += 5
    for m in range(257):
        x = F(m, 256)
        assert fabius(x) + fabius(1-x) == 1
        exact_checks += 1

    rows = []
    coefficient_cache = {}
    max_series_error = mp.mpf(0)
    min_bound_slack = mp.inf
    for M in (1, 2, 4, 8, 16):
        p, B, cs = coefficients(M)
        coefficient_cache[M] = (p, B, cs)
        selected = (F(0), F(1, 2)) if p % 2 else (F(1, 4), F(3, 4))
        delta = (1 - mp.mpf(2)**(-p-1)) * mp.zeta(p+1) - 1
        for j in range(32):
            theta = F(j, 32)
            for n in range(p):
                assert defect(M, theta, n) == 0
                exact_checks += 1
            exact = defect(M, theta, p)
            assert (exact == 0) == (theta in selected)
            exact_checks += 1
            approx = series_value(theta, p, B, cs)
            max_series_error = max(max_series_error, abs(approx - as_mp(exact)))
            tau = mp.cos(2*mp.pi*as_mp(theta) + p*mp.pi/2)
            if theta not in selected:
                observed = abs(as_mp(exact)/B - tau) / abs(tau)
                assert observed < delta
                min_bound_slack = min(min_bound_slack, delta - observed)
        rows.append({"M": M, "p": p, "selected_phase": str(selected[0]),
                     "E_p_at_1_8": str(defect(M, F(1, 8), p)),
                     "E_next_at_selected": str(defect(M, selected[0], p+1)),
                     "delta_p": mp.nstr(delta, 18),
                     "B_M": mp.nstr(B, 18)})
    # Exact, differently computed lattice-refinement tests.
    for M in (1, 2, 4):
        for L in (1, 2, 4, 8):
            for theta in (F(0), F(1, 8), F(3, 16)):
                for n in range(6):
                    lhs = sum((quadrature(M, theta + F(j, L), n)
                               for j in range(L)), F(0))/L
                    assert lhs == quadrature(M*L, L*theta, n)
                    exact_checks += 1

    ratio_checks = 0
    ratio_max = mp.mpf(0)
    sign_checks = 0
    for a in range(1, 64, 2):
        h0 = fourier_product(mp.mpf(a)/2)
        assert mp.sign(h0) == (-1)**(a.bit_count()-1)
        sign_checks += 1
        for k in range(3, 64, 2):
            ratio = abs(fourier_product(mp.mpf(a*k)/2)/h0) * k*k
            assert ratio <= 1 + mp.mpf('1e-50')
            ratio_checks += 1
            ratio_max = max(ratio_max, ratio)

    filter_checks = 0
    for n in range(1, 33):
        for L in range(1, 33):
            assert invariant(uniform_atoms(n, F(1, 7)), L) == (n % L == 0)
            filter_checks += 1
    # Signed weights obey the same invariance/orbit criterion.
    signed = [(x, 2*w) for x, w in uniform_atoms(4)] + [
        (x, -w) for x, w in uniform_atoms(4, F(1, 11))]
    assert invariant(signed, 4) and not invariant(signed, 8)
    assert sum(coalesce(signed).values(), F(0)) == 1
    filter_checks += 2

    report = {
        "status": "All checks passed; numerical diagnostics are not formal proofs.",
        "exact_quadrature_and_refinement_checks": exact_checks,
        "exact_filter_checks": filter_checks,
        "numerical_odd_multiplier_checks": ratio_checks,
        "numerical_binary_sign_checks": sign_checks,
        "maximum_series_absolute_discrepancy": mp.nstr(max_series_error, 10),
        "minimum_relative_bound_slack_on_test_grid": mp.nstr(min_bound_slack, 10),
        "maximum_k_squared_product_ratio_k_ge_3": mp.nstr(ratio_max, 10),
        "series_positive_odd_terms": 100,
        "product_factors": 120,
        "mpmath_decimal_precision": 65,
        "exact_samples": rows,
        "budget_examples": [
            {"mesh": str(M), "budget": N, **best_budget(M, N)}
            for M, N in [(F(12), 4), (F(12), 6), (F(3, 5), 4),
                         (F(3, 5), 5), (F(3, 5), 12), (F(8, 3), 13)]
        ],
    }
    (ROOT/'validation').mkdir(exist_ok=True)
    (ROOT/'validation'/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    if make_plot:
        import numpy as np
        import matplotlib
        matplotlib.use('Agg')
        matplotlib.rcParams['pdf.fonttype'] = 42
        import matplotlib.pyplot as plt
        phases = np.linspace(0, 1, 501)
        fig, ax = plt.subplots(figsize=(7.1, 3.65))
        for M in (1, 3, 5, 7):
            p, B, cs = coefficient_cache.get(M) or coefficients(M)
            values = np.zeros_like(phases)
            for k, c in zip(range(1, 2*len(cs), 2), cs):
                values += float(c)*np.cos(2*np.pi*k*phases + p*np.pi/2)
            ax.plot(phases, values, label=f'M = {M}', linewidth=1.5)
        ax.plot(phases, -np.sin(2*np.pi*phases), '--',
                label='First harmonic', linewidth=1.3)
        ax.set_xlabel(r'Phase $\theta$')
        ax.set_ylabel(r'Normalized first defect $E_{1,M}(\theta)/B_M$')
        ax.set_xticks([0, .25, .5, .75, 1])
        ax.grid(True, alpha=.25)
        ax.legend(ncol=3, fontsize=8, loc='upper right')
        fig.tight_layout()
        fig.savefig(ROOT/'figures'/'normalized_defect.pdf')
        fig.savefig(ROOT/'figures'/'normalized_defect.png', dpi=180)
        plt.close(fig)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plot', action='store_true', help='also regenerate the figure')
    args = parser.parse_args()
    main(args.plot)
