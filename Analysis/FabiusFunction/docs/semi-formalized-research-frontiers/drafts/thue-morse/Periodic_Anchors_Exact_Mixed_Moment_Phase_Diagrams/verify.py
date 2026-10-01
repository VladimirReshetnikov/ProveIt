#!/usr/bin/env python3
"""Exact algebraic checks and independent floating-point diagnostics.

Run: python verify.py --out verification_results.json
Optional figures: python verify.py --figures
Dependencies: Python >=3.10, NumPy, SciPy; Matplotlib only for --figures.
The exact checks use Python integers. Quadrature checks are diagnostics,
not interval enclosures or substitutes for the proofs in article.tex.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.special import logsumexp
from scipy.integrate import quad

# Exact arithmetic in Z[eta], eta^2 + eta + 2 = 0.
Pair = tuple[int, int]
ZERO: Pair = (0, 0)
ONE: Pair = (1, 0)
def add(a: Pair, b: Pair) -> Pair:
    return (a[0] + b[0], a[1] + b[1])
def neg(a: Pair) -> Pair:
    return (-a[0], -a[1])
def sub(a: Pair, b: Pair) -> Pair:
    return add(a, neg(b))
def mul(a: Pair, b: Pair) -> Pair:
    x, y = a; u, v = b
    return (x*u - 2*y*v, x*v + y*u - y*v)
def norm(a: Pair) -> int:
    x, y = a
    return x*x - x*y + 2*y*y
ETA = (0, 1)
ETABAR = (-1, -1)
D = [(-1, 0), ETABAR, neg(ETA), ONE]  # Ascending coefficients.
H = [(-1, 0), neg(ETABAR), ONE, neg(ETA), (-1, 0), ZERO, ZERO]

def exact_seventh_root_checks(max_n: int = 12) -> dict:
    tables = {}
    for R in (1, 2, 4):
        arr = []
        for k in range(7):
            u = sub(mul(ETABAR, H[k]), H[(k+R) % 7])
            v = sub(sub(mul(ETABAR, H[(k+R) % 7]), H[(k+2*R) % 7]),
                    mul(ETA, H[k]))
            arr.append(norm(H[k]) + norm(u) + norm(v))
        tables[str(R)] = arr
    assert tables == {
        '1': [1, 5, 4, 4, 5, 1, 1],
        '2': [3, 3, 4, 8, 4, 3, 3],
        '4': [7, 7, 3, 3, 2, 3, 3]}
    rows = []
    for n in range(max_n + 1):
        N = 2**n
        num = [ZERO] * (3*N + 1)
        for j, d in enumerate(D):
            num[j*N] = d
        quotient = [ZERO] * (3*N - 2)
        for k in range(3*N - 3, -1, -1):
            a = num[k+3]
            quotient[k] = a
            for j, d in enumerate(D):
                num[k+j] = sub(num[k+j], mul(a, d))
        assert all(a == ZERO for a in num), (n, 'nonzero remainder')
        actual = sum(norm(a) for a in quotient)
        expected = (3*N - 2) if n % 3 == 0 else (4*N - 2 if n % 3 == 1 else 4*N + 4)
        assert actual == expected, (n, actual, expected)
        rows.append({'n': n, 'N': N, 'moment': actual, 'formula': expected})
    return {'norm_tables': tables, 'exact_polynomial_checks': rows,
            'all_exact_checks_passed': True}

def mask(b: int, x: np.ndarray) -> np.ndarray:
    """Stable normalized finite Fourier sum; supports arbitrary real x."""
    y = np.remainder(x + 0.5, 1.0) - 0.5
    return np.abs(np.sinc(b*y) / np.sinc(y))

def phi(x: np.ndarray, cycles: list[list[float]], a: list[float]) -> np.ndarray:
    result = np.ones_like(x, dtype=float)
    for O, exponent in zip(cycles, a):
        for p in O:
            result *= np.abs(np.sin(np.pi*(x-p)))**exponent
    return result

def coboundary_checks() -> dict:
    rng = np.random.default_rng(20260930)
    examples = [(2, [[0.0], [1/3, 2/3]], [0.65, 1.7]),
                (3, [[0.0], [0.5], [0.25, 0.75]], [0.6, 1.2, 0.8])]
    rows = []
    for b, cycles, a in examples:
        x = rng.uniform(0.001, 0.999, 1000)
        lhs = np.ones_like(x)
        Dtot = sum(len(O)*v for O, v in zip(cycles, a))
        for O, exponent in zip(cycles, a):
            for p in O:
                lhs *= mask(b, x-p)**exponent
        rhs = b**(-Dtot)*phi(b*x, cycles, a)/phi(x, cycles, a)
        scale = np.maximum(np.maximum(lhs, rhs), 1e-12)
        err = float(np.max(np.abs(lhs-rhs)/scale))
        assert err < 2e-9
        rows.append({'base': b, 'maximum_scaled_error': err})
    return {'seed': 20260930, 'checks': rows}

def periodic_energy_checks() -> dict:
    b = 2
    cycles = [[Fraction(0)], [Fraction(1, 3), Fraction(2, 3)]]
    a = [0.65, 1.7]
    Dtot = a[0] + 2*a[1]
    rows = []
    for period in (3, 4, 5, 6, 7):
        p = Fraction(1, 2**period-1)
        orbit = sorted({Fraction((2**j * p) % 1) for j in range(period)})
        if set(orbit) & set(sum(cycles, [])):
            continue
        x = np.array([float(q) for q in orbit])
        values = np.zeros_like(x)
        for O, exponent in zip(cycles, a):
            for q in O:
                values += exponent*np.log(mask(b, x-float(q)))
        error = abs(float(np.mean(values)) + Dtot*math.log(2))
        assert error < 2e-10
        rows.append({'period': period, 'absolute_energy_error': error})
    return {'checks': rows}

def mixed_moment_diagnostics(oversampling: int = 64) -> dict:
    cases = [(0.4, 0.7), (3.0, 0.5), (0.3, 4.0), (1.0, 2.0)]
    rows = []
    for n in (6, 8, 10, 12):
        N = 2**n
        x = (np.arange(oversampling*N, dtype=float)+0.5)/(oversampling*N)
        tiny = np.finfo(float).tiny
        logbase = np.full_like(x, 2*math.log(N))
        for j in range(n):
            logbase += 2*np.log(np.maximum(np.abs(np.cos(np.pi*(2**j*x-0.25))), tiny))
        r0 = np.log(np.maximum(np.abs(np.sin(np.pi*N*x)), tiny)) \
             - np.log(np.maximum(np.abs(np.sin(np.pi*x)), tiny))
        r2 = np.zeros_like(x)
        for p in (1/3, 2/3):
            r2 += np.log(np.maximum(np.abs(np.sin(np.pi*(N*x-p))), tiny)) \
                  -np.log(np.maximum(np.abs(np.sin(np.pi*(x-p))), tiny))
        for a, d in cases:
            logI = float(logsumexp(logbase+a*r0+d*r2)-math.log(len(x)))
            gamma = 1+max(0, a-1, d-2)
            rows.append({'n': n, 'N': N, 'a': a, 'd': d,
                         'predicted_exponent': gamma,
                         'log_moment': logI,
                         'moment_divided_by_predicted_power': math.exp(logI-gamma*math.log(N))})
    rates = []
    for a, d in cases:
        selected = [r for r in rows if r['a'] == a and r['d'] == d]
        r, s = selected[-2:]
        rates.append({'a': a, 'd': d, 'predicted_exponent': s['predicted_exponent'],
                      'last_two_level_effective_exponent':
                      (s['log_moment']-r['log_moment'])/math.log(s['N']/r['N'])})
    return {'oversampling': oversampling, 'quadrature': 'midpoint; not certified',
            'phase': 0.25, 'values': rows, 'effective_exponents': rates}

def critical_crossover_diagnostics() -> dict:
    # Fixed point 0 is critical; the period-two orbit has exponent 0.6.
    cycles = [[0.0], [1/3, 2/3]]
    a0 = [1.0, 0.6]
    f = lambda t: float(phi(np.array([t]), cycles, a0)[0])
    mean_phi = sum(quad(f, l, r, epsabs=1e-11, epsrel=1e-11)[0]
                   for l, r in zip([0, 1/3, 2/3], [1/3, 2/3, 1]))
    cp = math.pi * abs(math.sin(math.pi/3)*math.sin(2*math.pi/3))**0.6
    coefficient = 2*mean_phi/cp
    rows = []
    for n in (6, 8, 10, 12):
        N = 2**n
        x = (np.arange(64*N, dtype=float)+0.5)/(64*N)
        for u in (-2.0, 0.0, 2.0):
            a = [1+u/math.log(N), 0.6]
            actual = float(np.mean(phi(N*x, cycles, a)/phi(x, cycles, a)))
            psi = math.expm1(u)/u if u else 1.0
            main = coefficient*math.log(N)*psi
            rows.append({'n': n, 'u': u, 'moment': actual, 'main_term': main,
                         'difference': actual-main})
    return {'coefficient': coefficient, 'values': rows,
            'status': 'floating-point diagnostic of a uniform O(1) remainder'}

def make_figures(outdir: Path, results: dict) -> None:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    outdir.mkdir(parents=True, exist_ok=True)
    a = np.linspace(0, 4, 401); d = np.linspace(0, 4, 401)
    aa, dd = np.meshgrid(a, d)
    scores = np.stack([np.zeros_like(aa), aa-1, dd-2])
    region = np.argmax(scores, axis=0)
    fig, ax = plt.subplots(figsize=(6.7, 4.5))
    ax.contourf(aa, dd, region, levels=[-0.5, 0.5, 1.5, 2.5], alpha=0.35)
    ax.plot([1, 1], [0, 2], linewidth=1.5)
    ax.plot([0, 1], [2, 2], linewidth=1.5)
    ax.plot([1, 3], [2, 4], linewidth=1.5)
    ax.plot([1], [2], 'o', markersize=5)
    ax.text(0.18, 0.8, 'Background')
    ax.text(2.1, 1.0, 'Fixed point 0')
    ax.text(0.2, 3.25, 'Period-two orbit')
    ax.annotate('Triple coexistence (1, 2)', (1, 2), (1.45, 2.55),
                arrowprops={'arrowstyle': '->'}, fontsize=9)
    ax.set(xlabel='Fixed-point exponent a', ylabel='Period-two exponent d',
           xlim=(0, 4), ylim=(0, 4), title='Binary squared background at phase c = 1/4')
    fig.tight_layout(); fig.savefig(outdir/'phase_diagram.pdf'); plt.close(fig)
    rows = results['exact_algebra']['exact_polynomial_checks']
    fig, ax = plt.subplots(figsize=(6.7, 3.8))
    for residue in range(3):
        selected = [x for x in rows if x['n'] % 3 == residue]
        ax.plot([x['n'] for x in selected], [x['moment']/x['N'] for x in selected],
                marker='o', label=f'n = {residue} mod 3')
    ax.set(xlabel='n', ylabel='Exact moment divided by 2^n',
           title='A periodic leading amplitude: 3, 4, 4')
    ax.legend(); ax.grid(alpha=0.2)
    fig.tight_layout(); fig.savefig(outdir/'periodic_amplitude.pdf'); plt.close(fig)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('verification_results.json'))
    parser.add_argument('--figures', action='store_true')
    args = parser.parse_args()
    results = {'exact_algebra': exact_seventh_root_checks(),
               'coboundary': coboundary_checks(),
               'periodic_energy': periodic_energy_checks(),
               'mixed_moments': mixed_moment_diagnostics(),
               'critical_crossover': critical_crossover_diagnostics()}
    args.out.write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')
    if args.figures:
        make_figures(args.out.parent/'figures', results)
    print('All exact assertions and numerical identity checks passed.')
    print('Exact polynomial divisions: n=0,...,12; largest N=4096.')
    for r in results['mixed_moments']['effective_exponents']:
        print('Mixed moment:', r)
    print('Critical-window remainder range:',
          min(r['difference'] for r in results['critical_crossover']['values']),
          max(r['difference'] for r in results['critical_crossover']['values']))
    print('Saved', args.out)

if __name__ == '__main__':
    main()
