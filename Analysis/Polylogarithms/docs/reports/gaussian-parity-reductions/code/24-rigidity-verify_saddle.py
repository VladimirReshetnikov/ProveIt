#!/usr/bin/env python3
"""Independent high-precision diagnostics for the proportional-depth theorem.

The mathematical error bounds are proved in the article. These are numerical
diagnostics, not interval certificates. Run from any directory.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import mpmath as mp


def saddle_data(alpha, a):
    alpha, a = mp.mpf(alpha), mp.mpf(a)
    L = lambda x: mp.log1p(mp.exp(-x))
    w = lambda x: 1 / ((1 + mp.exp(x)) * L(x))
    x = mp.findroot(lambda t: t * w(t) - alpha,
                    (alpha, 2 * alpha * mp.log(2)))
    phi = lambda t: alpha * mp.log(t) + mp.log(L(t))
    g = lambda t: mp.exp(-a * t) / (t * (1 + mp.exp(-t)))
    A = alpha / x**2 + mp.diff(w, x)
    I = -alpha * mp.log(x / alpha) - alpha - mp.log(L(x))
    C = mp.sqrt(alpha / A) * mp.exp(a * (alpha - x)) / (x * (1 + mp.exp(-x)))
    f3, f4 = mp.diff(phi, x, 3), mp.diff(phi, x, 4)
    E = (mp.diff(g, x, 2) / (2 * A * g(x))
         + f3 * mp.diff(g, x) / (2 * A**2 * g(x))
         + f4 / (8 * A**2) + 5 * f3**2 / (24 * A**3))
    D = E - alpha * a**2 / 2 - 1 / (12 * alpha)
    return x, A, I, C, D, phi, g


def normalized_integral(h, alpha, a, data):
    x, A, I, C, D, phi, g = data
    h, alpha, a = mp.mpf(h), mp.mpf(alpha), mp.mpf(a)
    px, gx = phi(x), g(x)
    def integrand(y):
        if not y:
            return mp.mpf(0)
        return mp.exp(h * (phi(y) - px)) * g(y) / gx
    integral = mp.quad(integrand, [0, x/2, x, 3*x/2, 2*x, mp.inf])
    log_R = (alpha*h*mp.log(h+a) - mp.loggamma(alpha*h)
             + h*px + mp.log(gx) + mp.log(integral))
    return mp.exp(log_R)


def verify(dps=70):
    mp.mp.dps = dps
    rows = []
    for alpha in (mp.mpf('0.25'), mp.mpf(1), mp.mpf(3)):
        for a in (mp.mpf('0.5'), mp.mpf('1.2')):
            data = saddle_data(alpha, a)
            x, A, I, C, D = data[:5]
            assert I > 0 and alpha < x < 2*alpha*mp.log(2)
            for h in (20, 40, 80, 160):
                exact = normalized_integral(h, alpha, a, data)
                leading = C * mp.exp(-h*I)
                quotient = exact/leading
                residual = quotient - 1 - D/h
                rows.append({
                    'alpha': str(alpha), 'a': str(a), 'h': h,
                    'x_alpha': mp.nstr(x, 45), 'rate': mp.nstr(I, 45),
                    'C': mp.nstr(C, 45), 'D': mp.nstr(D, 45),
                    'R': mp.nstr(exact, 45),
                    'relative_first_order_error': mp.nstr(quotient-1, 30),
                    'relative_second_order_error': mp.nstr(residual, 30),
                    'h_squared_times_error': mp.nstr(h*h*residual, 25)
                })
    # Independent differentiation check of the optimized rate.
    rate_checks = []
    for alpha in (mp.mpf('0.1'), mp.mpf(1), mp.mpf(5)):
        x = saddle_data(alpha, mp.mpf('0.5'))[0]
        numerical = mp.diff(lambda v: saddle_data(v, mp.mpf('0.5'))[2], alpha)
        formula = mp.log(alpha/x)
        residual = numerical-formula
        assert abs(residual) < mp.mpf(10)**(-dps+10)
        rate_checks.append({'alpha': str(alpha), 'residual': mp.nstr(residual, 10)})
    return {'precision_decimal_digits': dps, 'mpmath_version': mp.__version__,
            'status': 'numerical diagnostics; not interval certified',
            'quadrature_rows': rows, 'rate_derivative_checks': rate_checks}


def make_figure(output):
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    mp.mp.dps = 30
    alphas = np.linspace(.02, 10, 180)
    rates, prefactors = [], []
    for alpha in alphas:
        _, _, I, C, *_ = saddle_data(str(alpha), '0.5')
        rates.append(float(I)); prefactors.append(float(C))
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                         'axes.spines.top': False, 'axes.spines.right': False})
    fig, ax = plt.subplots(1, 2, figsize=(10, 3.65), layout='constrained')
    ax[0].semilogy(alphas, rates, color='#153c58', lw=2.2, label=r'$I(\alpha)$')
    ax[0].semilogy(alphas, .5*np.exp(-alphas), '--', color='#be7c39', lw=1.4,
                   label=r'$e^{-\alpha}/2$')
    ax[0].set(xlabel=r'$\alpha=p/h$', ylabel='Exponential rate',
              title='Rate of cancellation')
    ax[0].legend(frameon=False)
    ax[1].plot(alphas, prefactors, color='#257b79', lw=2.2)
    ax[1].set(xlabel=r'$\alpha=p/h$', ylabel=r'$C(\alpha,1/2)$',
              title='Gaussian prefactor', ylim=(.45, 1.03))
    for axis in ax:
        axis.grid(alpha=.2)
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output.with_suffix('.pdf'))
    fig.savefig(output.with_suffix('.png'), dpi=200)
    plt.close(fig)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    root = Path(__file__).resolve().parents[1]
    parser.add_argument('--output', type=Path, default=root/'results'/'saddle_verification.json')
    parser.add_argument('--dps', type=int, default=70)
    parser.add_argument('--figure', action='store_true')
    args = parser.parse_args()
    report = verify(args.dps)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    if args.figure:
        make_figure(root/'figures'/'saddle_rate')
    print(json.dumps({'output': str(args.output), 'quadrature_rows': len(report['quadrature_rows']),
                      'rate_checks': len(report['rate_derivative_checks'])}))
