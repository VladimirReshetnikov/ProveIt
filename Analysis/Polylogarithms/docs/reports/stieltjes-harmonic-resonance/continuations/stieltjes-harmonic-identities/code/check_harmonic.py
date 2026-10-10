#!/usr/bin/env python3
"""Independent high-precision quadrature checks for sections/harmonic.tex.

The quadrature evaluates the Mellin kernel obtained from the ordinary
harmonic generating function.  The other side uses finite polygamma
expressions, not a differentiated copy of the quadrature.

Finite-part checks use a subtracted Mellin integral.  The subtraction
contains only the local leading singularity; its remaining constant is
compared with the finite Gamma coefficient.  A small-t expansion avoids
catastrophic cancellation below 10**(-30).  Its integrated omitted term
is below the reported numerical gate, but these tests are numerical
corroboration, not interval-arithmetic proof certificates.
"""

import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 70
ROOT = Path(__file__).resolve().parent
rows = []


def record(name, lhs, rhs, tol=mp.mpf('1e-45')):
    error = abs(lhs - rhs)
    rows.append({
        'name': name,
        'lhs': mp.nstr(lhs, 55),
        'rhs': mp.nstr(rhs, 55),
        'abs_error': mp.nstr(error, 10),
        'gate': str(tol),
        'passed': bool(error < tol),
    })
    print(f"{name}: error={mp.nstr(error, 4)} {'PASS' if error < tol else 'FAIL'}", flush=True)


def coefficients(a):
    A = mp.euler + mp.digamma(a)
    B = mp.zeta(2) - mp.polygamma(1, a)
    C = mp.zeta(3) + mp.polygamma(2, a) / 2
    D = mp.zeta(4) - mp.polygamma(3, a) / 6
    return [mp.mpf(1), A, (A*A+B)/2,
            (A**3+3*A*B+2*C)/6,
            (A**4+6*A*A*B+3*B*B+8*A*C+6*D)/24]


def finite_square_cube(a, r, s):
    cs = coefficients(a)
    p = [None] + [mp.polygamma(j, a) for j in range(1, 6)]
    if s == 2:
        return mp.fsum((-1)**(j+1)*p[j]*cs[r+1-j]/mp.factorial(j)
                       for j in range(1, r+2))
    u = [None, p[2], p[1]**2-p[3]/2,
         p[4]/6-p[1]*p[2], -p[5]/24+p[1]*p[3]/3+p[2]**2/4]
    return -mp.fsum(cs[r+1-j]*u[j] for j in range(1, r+2))/2


def mellin_kernel(t, a, r):
    if not t:
        return mp.mpf(0)  # Endpoints have measure zero.
    d = -mp.expm1(-t)
    return mp.exp(-a*t)*(-mp.log(d))**r / (mp.factorial(r)*d)


def mellin_value(a, r, s):
    f = lambda t: t**(s-1)*mellin_kernel(t, a, r)
    return mp.quad(f, [0, mp.mpf('.001'), mp.mpf('.1'), 1, 4, 12, mp.inf])/mp.gamma(s)


def mellin_remainder(a, r, k=0):
    def local(t):
        if not t:
            return mp.mpf(0)
        L = -mp.log(t)
        if t < mp.mpf('1e-30'):
            val = (mp.mpf('.5')-a)*L**r
            if r:
                val += r*L**(r-1)/2
            val /= mp.factorial(r)
        else:
            val = mellin_kernel(t, a, r)-L**r/(mp.factorial(r)*t)
        return mp.log(t)**k*val

    def tail(t):
        return mp.log(t)**k*mellin_kernel(t, a, r)

    return (mp.quad(local, [0, mp.mpf('1e-15'), mp.mpf('.001'), mp.mpf('.1'), 1])
            + mp.quad(tail, [1, 4, 12, mp.inf]))/mp.factorial(k)


def quadratic_value(a, b, r):
    return mp.quad(lambda t: mp.sin(b*t)*mellin_kernel(t, a, r)/b,
                   [0, mp.mpf('.001'), mp.mpf('.1'), 1, 4, 12, mp.inf])


for a in [mp.mpf('.5'), mp.mpf('1.3')]:
    for r in range(4):
        for s in [2, 3]:
            record(f'polygamma_table a={a} r={r} s={s}',
                   mellin_value(a, r, s), finite_square_cube(a, r, s))
        record(f'finite_part_remainder a={a} r={r}',
               mellin_remainder(a, r), -coefficients(a)[r+1])

ac = mp.mpc('1.2', '.4')
for r in [0, 1, 3]:
    record(f'complex_table a=1.2+0.4i r={r} s=2',
           mellin_value(ac, r, 2), finite_square_cube(ac, r, 2))
    record(f'complex_finite_part r={r}',
           mellin_remainder(ac, r), -coefficients(ac)[r+1])

a, b = mp.mpf('1.3'), mp.mpf('.7')
for r in range(4):
    rhs = (coefficients(a+1j*b)[r+1]-coefficients(a-1j*b)[r+1])/(2j*b)
    record(f'quadratic_kernel r={r}', quadratic_value(a, b, r), rhs)

# Checks the ordinary Stieltjes layer, including the conventional sign.
g2 = (mp.euler**2-mp.zeta(2))/2
for a in [mp.mpf('.5'), mp.mpf('1.3')]:
    raw_linear = g2 + mp.euler*mellin_remainder(a, 0) + mellin_remainder(a, 0, 1)
    record(f'stieltjes_linear a={a}', raw_linear, -mp.stieltjes(1, a))

L = mp.log(2)
half3 = (31*mp.zeta(5)-13*mp.zeta(2)*mp.zeta(3)-15*L*mp.zeta(4)
         +14*L**2*mp.zeta(3)-4*L**3*mp.zeta(2))
record('half_point_cubic_expansion', mellin_value(mp.mpf('.5'), 3, 2), half3)

summary = {
    'precision_dps': mp.mp.dps,
    'tests': len(rows),
    'passed': sum(row['passed'] for row in rows),
    'maximum_absolute_residual': mp.nstr(max(mp.mpf(row['abs_error']) for row in rows), 12),
    'certification': 'Numerical cross-checks only; proofs are in sections/harmonic.tex.',
    'results': rows,
}
(ROOT.parent/'data'/'harmonic_checks.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
raise SystemExit(0 if summary['passed'] == summary['tests'] else 1)
