#!/usr/bin/env python3
"""Reproduce the Stieltjes-kernel and moving-zero checks in the article.

Numerical checks are not interval certificates and do not prove zero counts.
The manuscript supplies the proofs; this script checks constants, signs,
normalizations, and the first two asymptotic corrections independently of
the typeset formulas.  Run from any directory.  Requires mpmath, numpy,
scipy, matplotlib.  Output is deterministic up to numerical library versions.
"""

from functools import lru_cache
from pathlib import Path
import json
import platform

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 85


@lru_cache(None)
def poly_coefficients(n):
    c = mp.taylor(lambda z: mp.rgamma(1 + z), 0, n)
    return tuple(mp.binomial(n, j) * mp.factorial(j) * c[j]
                 for j in range(n + 1))


def poly(n, x):
    return mp.polyval(poly_coefficients(n), x)


def kernel(n, t):
    return poly(n, mp.log(t)) / (-mp.expm1(-t))


@lru_cache(None)
def harmonic_coefficients(k, n):
    e = [mp.mpf(1)] + [mp.mpf(0)] * n
    for j in range(1, k + 1):
        for i in range(min(j, n), 0, -1):
            e[i] += e[i - 1] / j
    return tuple(e)


def poly_multiply(a, b, n):
    return [mp.fsum(a[j]*b[i-j] for j in range(i+1)
                    if j < len(a) and i-j < len(b)) for i in range(n+1)]


def normalized_hurwitz(n, k, a, extra_terms=0):
    """Scaled Euler--Maclaurin evaluation of a**(k+1) F_{n,k}(a)/k!.

    Applying an absolute-tolerance zeta implementation before multiplying by
    a**(k+1) loses accuracy when the unscaled zeta value is extremely small.
    All summands below are scaled *before* evaluation.  Truncated power
    series in z retain the needed n-th s-jet without finite differencing.
    The stopping test is numerical, not an interval remainder certificate.
    Each reported root is checked again after increasing the finite sum.
    """
    K = k + 1
    e = harmonic_coefficients(k, n)
    N = max(40, int(mp.mp.dps) + K//4) + extra_terms
    head = []
    for m in range(N):
        x = a + m
        logx = mp.log(x)
        coefficient = mp.fsum(e[i]*(-logx)**(n-i)/mp.factorial(n-i)
                              for i in range(n+1))
        head.append(mp.exp(-K*mp.log1p(m/a))*coefficient)
    v = a + N
    tail = [v*(-1)**j/mp.mpf(k)**(j+1) for j in range(n+1)]
    tail[0] += mp.mpf('.5')
    rising = [mp.mpf(K)/v, 1/v] + [mp.mpf(0)]*max(0, n-1)
    rising = rising[:n+1]
    for r in range(1, 1000):
        factor = mp.bernoulli(2*r)/mp.factorial(2*r)
        terms = [factor*c for c in rising]
        tail = [tail[j] + terms[j] for j in range(n+1)]
        if max(abs(z) for z in terms) < mp.eps*mp.mpf('1e-8'):
            break
        for c in (K + 2*r - 1, K + 2*r):
            rising = poly_multiply(rising, [mp.mpf(c)/v, 1/v], n)
    else:
        raise ArithmeticError('Euler--Maclaurin series did not reach tolerance')
    exp_coeff = [(-mp.log(v))**j/mp.factorial(j) for j in range(n+1)]
    tail_coefficient = poly_multiply(poly_multiply(e, exp_coeff, n), tail, n)[n]
    return mp.factorial(n)*(mp.fsum(head)
                           + mp.exp(-K*mp.log1p(N/a))*tail_coefficient)


def raw_laplace(n, k, a):
    def f(t):
        if t == 0 or mp.isinf(t):
            return mp.mpf(0)
        return t**k * mp.exp(-a*t) * kernel(n, t)
    return mp.quad(f, [0, mp.mpf('0.25'), 1, 4, 16, mp.inf])


def decimal(x, digits=60):
    return mp.nstr(x, digits)


def root_constants(n, rho):
    t = mp.exp(rho)
    h1 = mp.diff(lambda u: kernel(n, u), t)
    b2, b3, b4 = [mp.diff(lambda u: kernel(n, u), t, r) / h1
                  for r in (2, 3, 4)]
    offset = b2 / 2
    correction = (t*(b3/3 - b2*b2/4)
                  + t*t*(b4 - 2*b2*b3 + b2**3)/8)
    # Independently reconstruct the zero expansion before reciprocating.
    A = t*t*mp.diff(lambda u: kernel(n, u), t, 2)/2
    A1 = mp.diff(lambda u: u*u*mp.diff(lambda v: kernel(n, v), u, 2)/2, t)
    B = (t**3*mp.diff(lambda u: kernel(n, u), t, 3)/3
         + t**4*mp.diff(lambda u: kernel(n, u), t, 4)/8)
    u1 = -A/h1
    u2 = -(mp.diff(lambda u: kernel(n, u), t, 2)*u1*u1/2 + A1*u1 + B)/h1
    assert abs(correction - (u1*u1/t**3 - u2/t**2)) < mp.mpf('1e-70')
    return t, offset, correction


def make_figures():
    import numpy as np
    from scipy.special import roots_genlaguerre, gamma
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt

    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.labelsize': 9, 'axes.titlesize': 11,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'pdf.fonttype': 42, 'ps.fonttype': 42})
    fig, axes = plt.subplots(1, 3, figsize=(10.2, 3.5), layout='constrained')
    colors = {16: '#bc6c25', 64: '#1d7874'}
    for n, ax in enumerate(axes, 1):
        rhos = sorted(float(mp.re(r)) for r in mp.polyroots(poly_coefficients(n)))
        x = np.linspace(rhos[0] - .55, rhos[-1] + .55, 330)
        ts = np.exp(x)
        coeff = np.array([float(v) for v in poly_coefficients(n)])
        ax.plot(x, np.polyval(coeff, x), color='#1b263b', lw=1.7,
                label=r'$P_n(x)$')
        for K in (16, 64):
            nodes, weights = roots_genlaguerre(160, K - 1)
            weights /= gamma(K)
            sample_t = ts[:, None] * nodes[None, :] / K
            h = np.polyval(coeff, np.log(sample_t)) / (-np.expm1(-sample_t))
            vals = (-np.expm1(-ts)) * (h @ weights)
            ax.plot(x, vals, color=colors[K], lw=1.15,
                    linestyle='--' if K == 16 else '-.', label=f'K = {K}')
        ax.axhline(0, color='#a5acb8', lw=.65)
        ax.set_title(f'n = {n}')
        ax.set_xlabel(r'$x=\log t$')
        ax.grid(axis='y', alpha=.16)
    axes[0].set_ylabel('Normalized derivative profile')
    axes[-1].legend(frameon=False, loc='best', fontsize=8)
    out = ROOT / 'figures'
    out.mkdir(exist_ok=True)
    fig.savefig(out / 'stieltjes_profiles.pdf', bbox_inches='tight')
    fig.savefig(out / 'stieltjes_profiles.png', dpi=190, bbox_inches='tight')
    plt.close(fig)


def main():
    output = {'precision_decimal_digits': mp.mp.dps,
              'python': platform.python_version(), 'mpmath': mp.__version__,
              'status': 'Numerical diagnostics; not interval-certified proofs',
              'kernel_checks': [], 'moving_zeros': [], 'first_index_brackets': []}
    for n in range(4):
        for k in (1, 3):
            a = mp.sqrt(2) - 1 if k == 1 else mp.mpf('1.5')
            exact = normalized_hurwitz(n, k, a) * mp.factorial(k) / a**(k+1)
            integral = raw_laplace(n, k, a)
            error = abs(exact - integral) / max(1, abs(exact))
            assert error < mp.mpf('1e-65'), (n, k, error)
            output['kernel_checks'].append({'n': n, 'k': k, 'a': decimal(a),
                                           'relative_or_absolute_error': decimal(error)})

    for n in range(1, 5):
        rhos = sorted(mp.re(r) for r in mp.polyroots(poly_coefficients(n), maxsteps=1000))
        assert all(abs(poly(n, rho)) < mp.mpf('1e-70') for rho in rhos)
        for j, rho in enumerate(rhos, 1):
            t, offset, correction = root_constants(n, rho)
            for k in (8, 32, 128, 512):
                K = k + 1
                first = K/t + offset
                second = first + correction/K
                f = lambda a: normalized_hurwitz(n, k, a)
                root = mp.findroot(f, (second*mp.mpf('.995'), second*mp.mpf('1.005')),
                                   tol=mp.mpf('1e-73'), maxsteps=60)
                assert root > 0 and abs(f(root)) < mp.mpf('1e-65'), (n, k, j, root, f(root))
                independent_N_residual = abs(normalized_hurwitz(n, k, root, extra_terms=31))
                assert independent_N_residual < mp.mpf('1e-65')
                output['moving_zeros'].append({
                    'n': n, 'polynomial_root_index_increasing': j, 'k': k,
                    'rho': decimal(rho), 'limiting_slope': decimal(1/t),
                    'offset_for_K': decimal(offset), 'coefficient_of_1_over_K': decimal(correction),
                    'a': decimal(root), 'first_approximation': decimal(first),
                    'second_approximation': decimal(second),
                    'error_after_offset': decimal(abs(root-first)),
                    'error_after_1_over_K': decimal(abs(root-second)),
                    'K_squared_times_second_error': decimal(K*K*abs(root-second)),
                    'normalized_zero_residual': decimal(abs(f(root))),
                    'changed_summation_cutoff_residual': decimal(independent_N_residual)})

    for k in (1, 2, 4, 8, 16, 32, 64, 128):
        lower = mp.exp(mp.harmonic(k-1))
        upper = lower + mp.mpf('.5')
        f = lambda a: normalized_hurwitz(1, k, a)
        assert f(lower) > 0 and f(upper) < 0
        root = mp.findroot(f, (lower, upper), solver='anderson', tol=mp.mpf('1e-73'))
        assert lower < root < upper
        output['first_index_brackets'].append({'k': k, 'lower': decimal(lower),
                                               'a': decimal(root), 'upper': decimal(upper)})

    (ROOT / 'data').mkdir(exist_ok=True)
    (ROOT / 'data' / 'stieltjes_zero_checks.json').write_text(json.dumps(output, indent=2)+'\n')
    make_figures()
    print(json.dumps({'kernel_checks': len(output['kernel_checks']),
                      'moving_zero_checks': len(output['moving_zeros']),
                      'global_brackets': len(output['first_index_brackets']),
                      'all_passed': True}))


if __name__ == '__main__':
    main()
