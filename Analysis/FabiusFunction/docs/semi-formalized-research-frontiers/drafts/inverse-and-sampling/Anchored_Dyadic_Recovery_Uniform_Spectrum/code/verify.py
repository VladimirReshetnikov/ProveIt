#!/usr/bin/env python3
"""Regression checks for Anchored Dyadic Recovery.

Exact rational tests are separated from mpmath diagnostics. The tests do not
certify the analytic theorems. Run from any directory: python code/verify.py.

ed. (2026-09-29): outputs go to data-rerun/ beside data/ unless --output-dir
names another directory, so a plain run no longer overwrites the recorded
files in data/; all four files are written with LF line endings.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import argparse
import csv
import json
import platform
import sys
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
TAU = F(1, 1000)


def poly(roots: list[F]) -> list[F]:
    """Ascending monic polynomial coefficients."""
    c = [F(1)]
    for r in roots:
        d = [F(0)] * (len(c) + 1)
        for i, v in enumerate(c):
            d[i] -= r * v
            d[i+1] += v
        c = d
    return c


def evaluate(c: list[F], t: F) -> F:
    v = F(0)
    for a in reversed(c):
        v = v * t + a
    return v


def newton(c: list[F], degree: int) -> list[F]:
    """Power sums p_1,...,p_degree from a monic polynomial, exactly."""
    n = len(c) - 1
    assert c[-1] == 1
    p = [F(n)]
    for k in range(1, degree + 1):
        if k <= n:
            val = -sum((c[n-j] * p[k-j] for j in range(1, k)), F(0))
            val -= k * c[n-k]
        else:
            val = -sum((c[n-j] * p[k-j] for j in range(1, n+1)), F(0))
        p.append(val)
    return p[1:]


def exact_checks() -> dict[str, int]:
    counts = dict(root_intervals=0, unchanged_power_sums=0,
                  first_changed_power_sums=0, divisor_count_inversions=0,
                  polynomial_constant_changes=0)
    for n in range(2, 21):
        roots = [F(1, 16**j) for j in range(1, n+1)]
        c = poly(roots)
        delta = TAU * F(1, 16**(n*(n+1)//2))
        shifted = c.copy()
        shifted[0] -= delta
        assert all(c[i] == shifted[i] for i in range(1, n+1))
        counts['polynomial_constant_changes'] += 1
        for x in roots:
            lo, hi = 3*x/4, 5*x/4
            assert evaluate(shifted, lo) * evaluate(shifted, hi) < 0
            assert abs(evaluate(c, lo)) > delta
            assert abs(evaluate(c, hi)) > delta
            counts['root_intervals'] += 1
        p, ps = newton(c, n), newton(shifted, n)
        for k in range(n-1):
            assert p[k] == ps[k] == sum((x**(k+1) for x in roots), F(0))
            counts['unchanged_power_sums'] += 1
        assert ps[-1] - p[-1] == n*delta
        counts['first_changed_power_sums'] += 1
    primitive = [0]*513
    for m in range(1, 513):
        k, v2 = m, 0
        while k % 2 == 0:
            k //= 2
            v2 += 1
        primitive[m] = 1+v2-sum(primitive[d] for d in range(1, m) if m % d == 0)
        assert primitive[m] == int(m & (m-1) == 0)
        counts['divisor_count_inversions'] += 1
    assert 1 - 24*TAU/11 > F(1, 2)
    return counts


def bounds(n: int) -> dict[str, str | int]:
    """Evaluate proved upper bounds; not measurements of actual TV."""
    if n < 16:
        raise ValueError('n must be at least 16')
    tau = mp.mpf(1)/1000
    h, m, k = n//2, n//8, (3*n)//10
    T = mp.power(2, mp.mpf(3)*n/5)
    A = mp.mpf(5)/64
    D = 2*tau*h*mp.power(mp.mpf(4)/3, n)*mp.power(16, -(n-h)*(n-h+1)/2)
    r = mp.sqrt(mp.mpf(5)/4)*mp.power(4, -(h+1))*T/mp.pi
    assert r < 1
    E = T*D + 2*m*D/A*max(1, A*T*T/(mp.pi**2))**m
    E += 4*n*r**(2*m+2)/((m+1)*(1-r*r))
    high = 8*mp.power(2, 2*k*k)*T**(1-2*k)/(2*k-1)
    V = min(mp.mpf(1), mp.sqrt((2*T*E*E + high)/(2*mp.pi)))
    gap = tau*mp.power(4, -n)/3
    return {'n': n, 'gap_lower_bound': mp.nstr(gap, 14),
            'TV_upper_bound': mp.nstr(V, 14),
            'log10_gap_lower_bound': mp.nstr(mp.log10(gap), 16),
            'log10_TV_upper_bound': mp.nstr(mp.log10(V), 16),
            'minus_log_TV_over_n_squared': mp.nstr(-mp.log(V)/(n*n), 16)}


def rouche_threshold(M: int, L: int = 3) -> dict[str, str | int]:
    if M < 4 or L < 1:
        raise ValueError('M >= 4 and L >= 1 are required')
    eta = mp.mpf(1)/10
    r = 2*mp.pi*eta
    R = 2*mp.pi*(2*M+eta)
    J = int(mp.ceil(mp.log(2*R, 2)))
    logeps = -1-L*r-mp.log(4*(1+L*R)) + J*mp.log(4*eta/R)
    return {'M': M, 'J': J, 'log10_measurement_threshold': mp.nstr(logeps/mp.log(10), 15),
            'spectral_error_bound': mp.nstr(mp.mpf(1)/(2*M), 12)}


def numeric_roots(n: int) -> list[mp.mpf]:
    """Bracketed bisection, using a factored polynomial, not polyroots."""
    mp.mp.dps = max(100, 3*n*n + 50)
    xs = [mp.power(16, -j) for j in range(1, n+1)]
    delta = mp.mpf(1)/1000 * mp.power(16, -n*(n+1)//2)
    def p(z: mp.mpf) -> mp.mpf:
        return mp.fprod(z-x for x in xs)-delta
    ys = []
    for x in xs:
        a, b = mp.mpf(3)*x/4, mp.mpf(5)*x/4
        fa = p(a)
        assert fa*p(b) < 0
        for _ in range(int(mp.mp.dps*3.5)+10):
            mid = (a+b)/2
            fm = p(mid)
            if fm == 0:
                a=b=mid
                break
            if fa*fm < 0:
                b=mid
            else:
                a, fa = mid, fm
        ys.append((a+b)/2)
    return ys


def diagnostics() -> dict[str, object]:
    cases = []
    for n in [2, 4, 6, 8]:
        ys = numeric_roots(n)
        xs = [mp.power(16, -j) for j in range(1, n+1)]
        relative_errors = []
        for j, (x, y) in enumerate(zip(xs, ys), start=1):
            ell = n-j
            upper = mp.mpf(2)/1000 * (mp.mpf(4)/3)**ell * mp.power(16, -ell*(ell+1)//2)
            assert abs(y/x-1) <= upper*(1+mp.mpf('1e-30'))
            relative_errors.append(abs(mp.sqrt(y/x)-1))
        gap = abs(mp.sqrt(ys[-1])-mp.sqrt(xs[-1]))
        assert gap >= mp.mpf(1)/3000 * mp.power(4, -n)
        assert sum(relative_errors) <= mp.mpf(24)/11000
        residuals = []
        for k in range(1, n):
            px, py = sum(x**k for x in xs), sum(y**k for y in ys)
            residuals.append(abs((py-px)/px))
        cases.append({'n': n, 'precision_decimal_digits': mp.mp.dps,
                      'largest_relative_power_sum_residual': mp.nstr(max(residuals), 8),
                      'last_scale_gap_over_proved_lower_bound': mp.nstr(gap/(mp.power(4,-n)/3000), 12)})
    return {'note': 'Floating-point diagnostics, not interval certificates.', 'cases': cases}


def main() -> None:
    # ed. (2026-09-29): explicit output directory, default data-rerun/.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT/'data-rerun',
                        help='directory for the four output files '
                             '(default: data-rerun/ beside data/)')
    out = parser.parse_args().output_dir
    out.mkdir(parents=True, exist_ok=True)
    result = {'python': platform.python_version(), 'mpmath': mp.__version__,
              'exact_checks': exact_checks(), 'diagnostics': diagnostics()}
    mp.mp.dps = 90
    rows = [bounds(n) for n in [16, 32, 64, 128, 256, 512]]
    thresholds = [rouche_threshold(M) for M in [4, 16, 64, 256, 1024, 4096]]
    result['bounds'] = rows
    result['rouche_thresholds'] = thresholds
    report = json.dumps(result, indent=2) + '\n'
    # ed. (2026-09-29): LF line endings on every platform.
    (out/'verification.json').write_text(report, newline='\n')
    (out/'verification.txt').write_text(report, newline='\n')
    for name, data in [('analytic_bounds.csv', rows), ('rouche_thresholds.csv', thresholds)]:
        with (out/name).open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=data[0].keys(),
                                    lineterminator='\n')
            writer.writeheader(); writer.writerows(data)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
