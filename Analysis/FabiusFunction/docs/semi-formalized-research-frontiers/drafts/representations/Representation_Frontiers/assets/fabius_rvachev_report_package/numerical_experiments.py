#!/usr/bin/env python3
"""Reproducible checks for the Fabius--Rvachev representation report.

The script verifies:
  1. the dyadic sinc product against the Fredholm trace expansion;
  2. exact exterior-power coefficients and reciprocal-dyadic Fabius values;
  3. strict Newton--Turan inequalities;
  4. the Mellin--Barnes representation of the endpoint Laplace transform.

It writes CSV data and PNG figures into the directory containing this file.
"""
from __future__ import annotations

import csv
from pathlib import Path
from typing import Iterable, List

import matplotlib.pyplot as plt
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parent
mp.mp.dps = 50


def sinc(x):
    return mp.mpf(1) if x == 0 else mp.sin(x) / x


def phi_scale_product(t, levels: int = 120):
    ans = mp.mpf(1)
    for n in range(1, levels + 1):
        ans *= sinc(t / 2**n)
    return ans


def trace_B(s):
    return mp.zeta(2 * s) / (mp.pi ** (2 * s) * (4**s - 1))


def phi_trace_series(t, terms: int = 180):
    return mp.exp(mp.fsum(-t ** (2 * j) * trace_B(j) / j for j in range(1, terms + 1)))


def exact_power_trace(j: int) -> sp.Rational:
    return sp.simplify(sp.zeta(2 * j) / (sp.pi ** (2 * j) * (4**j - 1)))


def exterior_coefficients(max_n: int) -> List[sp.Rational]:
    """e_n(B)=Tr(wedge^n B) from Newton's identities."""
    e = [sp.Rational(0)] * (max_n + 1)
    e[0] = sp.Rational(1)
    for n in range(1, max_n + 1):
        e[n] = sp.simplify(sum((-1) ** (j - 1) * exact_power_trace(j) * e[n-j]
                               for j in range(1, n + 1)) / n)
    return e


def fabius_dyadic(n: int, e: List[sp.Rational]) -> sp.Rational:
    """Exact formula F(2^{-n})=2^{-n(n+1)/2} sum e_k/(n-2k)! ."""
    total = sum(e[k] / sp.factorial(n - 2*k) for k in range(n // 2 + 1))
    return sp.simplify(sp.Rational(1, 2) ** (n * (n + 1) // 2) * total)


def log_L_product(s, levels: int = 220):
    return mp.fsum(mp.log(-mp.expm1(-s / 2**j) / (s / 2**j))
                   for j in range(1, levels + 1))


def log_L_MB(s, c=mp.mpf('0.75'), cutoff=mp.mpf('35')):
    """Vertical Mellin--Barnes integral, using conjugation symmetry."""
    def integrand(y):
        u = c + 1j*y
        z = (mp.pi / (u * mp.sin(mp.pi*u))
             * (s / (2*mp.pi)) ** (2*u)
             * mp.zeta(2*u) / (4**u - 1))
        return mp.re(z)
    val = mp.quad(integrand, [0, 1, 3, 7, 15, cutoff]) / mp.pi
    return -s/2 + val


def write_csv(path: Path, header: Iterable[str], rows: Iterable[Iterable[object]]) -> None:
    with path.open('w', newline='', encoding='utf-8') as f:
        w = csv.writer(f, lineterminator='\n')
        w.writerow(list(header))
        w.writerows(rows)


def main() -> None:
    # Product / trace identity.
    ts = [mp.mpf(x) for x in ('0.25', '0.75', '1.5', '2.75', '4.0', '5.25')]
    rows = []
    for t in ts:
        p = phi_scale_product(t)
        q = phi_trace_series(t)
        rows.append([mp.nstr(t,12), mp.nstr(p,50), mp.nstr(q,50), mp.nstr(abs(p-q),12)])
    write_csv(OUT/'fourier_product_trace_checks.csv',
              ['t','dyadic_sinc_product','trace_exponential','absolute_error'], rows)

    t0 = mp.mpf('5.25')
    ref = phi_scale_product(t0, 180)
    counts = list(range(2, 82, 2))
    errs = [abs(phi_trace_series(t0, n)-ref) for n in counts]
    plt.figure(figsize=(7.2,4.4))
    plt.semilogy(counts, [float(x) for x in errs], marker='o', markersize=3)
    plt.xlabel('Number of trace-series terms')
    plt.ylabel('Absolute error at t=5.25')
    plt.title('Convergence of the Fredholm trace expansion')
    plt.grid(True, which='both', alpha=.3)
    plt.tight_layout(); plt.savefig(OUT/'trace_series_convergence.png', dpi=180); plt.close()

    # Exact exterior powers and dyadic values.
    e = exterior_coefficients(18)
    write_csv(OUT/'exterior_coefficients.csv',
              ['n','e_n_B','centered_even_moment_mu_2n','decimal_e_n'],
              ([n, str(e[n]), str(sp.simplify(sp.factorial(2*n)*e[n])), sp.N(e[n],18)]
               for n in range(19)))
    write_csv(OUT/'dyadic_exterior_values.csv',
              ['n','F_2_to_minus_n_exact','decimal'],
              ([n, str(fabius_dyadic(n,e)), sp.N(fabius_dyadic(n,e),25)] for n in range(16)))

    # Strict Newton inequalities.
    idx = list(range(1,15)); ratios=[]; bounds=[]; rows=[]
    for n in idx:
        ratio = sp.N(e[n]**2/(e[n-1]*e[n+1]),40)
        bound = sp.Rational(n+1,n)
        ratios.append(float(ratio)); bounds.append(float(bound))
        rows.append([n, ratio, bound, sp.N(ratio-bound,30)])
    write_csv(OUT/'turan_inequalities.csv',
              ['n','e_n_squared_over_neighbors','strict_lower_bound','gap'], rows)
    plt.figure(figsize=(7.2,4.4))
    plt.plot(idx, ratios, marker='o', label='observed ratio')
    plt.plot(idx, bounds, linestyle='--', label='(n+1)/n')
    plt.xlabel('n'); plt.ylabel('e_n^2 / (e_{n-1} e_{n+1})')
    plt.title('Strict Newton inequalities for normalized even moments')
    plt.grid(True, alpha=.3); plt.legend(); plt.tight_layout()
    plt.savefig(OUT/'turan_ratios.png', dpi=180); plt.close()

    # Mellin--Barnes check.
    ss = [mp.mpf(x) for x in ('0.5','2','10','50')]
    rows=[]; errs=[]
    for s in ss:
        direct=log_L_product(s); mb=log_L_MB(s); err=abs(direct-mb)
        rows.append([mp.nstr(s,12),mp.nstr(direct,50),mp.nstr(mb,50),mp.nstr(err,12)])
        errs.append(float(err))
    write_csv(OUT/'mellin_barnes_checks.csv',
              ['s','log_L_direct_product','log_L_Mellin_Barnes','absolute_error'], rows)
    plt.figure(figsize=(7.2,4.4))
    plt.loglog([float(s) for s in ss], errs, marker='o')
    plt.xlabel('s'); plt.ylabel('Absolute error')
    plt.title('Mellin--Barnes verification of the endpoint Laplace transform')
    plt.grid(True, which='both', alpha=.3); plt.tight_layout()
    plt.savefig(OUT/'mellin_barnes_errors.png', dpi=180); plt.close()

    print('Generated all checks in', OUT)
    for n in range(11):
        print(f'F(2^-{n}) = {fabius_dyadic(n,e)}')


if __name__ == '__main__':
    main()
