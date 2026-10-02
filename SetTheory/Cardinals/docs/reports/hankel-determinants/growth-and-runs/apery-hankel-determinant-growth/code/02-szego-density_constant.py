#!/usr/bin/env python3
"""Numerical evaluation of the Apéry density and its Szegő constant.
Requires mpmath. This is high-precision quadrature, NOT interval certification.
The analytic input is Edgar, arXiv:2005.10733v2, Propositions 23, 25, 26.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp


def constants():
    C = 17 + 12 * mp.sqrt(2)
    return C, 1 / C, (7 + 3 * mp.sqrt(5)) / 2


def hyper(z):
    return mp.hyp2f1(mp.mpf(1) / 3, mp.mpf(2) / 3, 1, z)


def density(x):
    """Evaluate phi(x), 0<x<C, with the continuation sheet specified explicitly."""
    C, c, scut = constants()
    x = mp.mpf(x)
    if not 0 < x < C:
        raise ValueError("Density evaluation requires 0 < x < C.")
    if x < c:
        d = mp.sqrt(x*x - 34*x + 1)
        a = x**3 + 30*x*x - 24*x + 1
        b = (x*x - 7*x + 1) * d
        lm = (a-b) / (2*(x+1)**3)
        lp = (a+b) / (2*(x+1)**3)
        return 4*mp.sqrt(3)/(mp.pi*(x+1))*hyper(lm)*hyper(lp)
    s = 1/x
    d = 1j*mp.sqrt(-(s*s - 34*s + 1))
    mu_squared = (3-3*s-d)/(2*(s+1)**2)
    lam = (s**3+30*s*s-24*s+1-(s*s-7*s+1)*d)/(2*(s+1)**3)
    F = hyper(lam)
    # Continue from the upper to the lower side across the hypergeometric cut.
    if s > scut:
        F += 1j*mp.sqrt(3)*hyper(1-lam)
    return -mp.im(mu_squared*F*F/x)/mp.pi


def log_density_angle(t):
    """x=C*sin(t/2)^2; use endpoint expansions to prevent cancellation.
    The fixed 1e-8 cutoff means reported extra digits are NOT an error bound.
    """
    C, _, _ = constants()
    if t < mp.mpf('1e-8'):
        logx = mp.log(C) + 2*mp.log(mp.sin(t/2))
        return mp.log(-6*logx/mp.pi**2)
    if mp.pi-t < mp.mpf('1e-8'):
        return (-mp.mpf(5)/4*mp.log(2)-mp.log(C)/2
                -2*mp.log(mp.pi)+mp.log(mp.cos(t/2)))
    return mp.log(density(C*mp.sin(t/2)**2))


def evaluate(dps=40):
    if dps < 25:
        raise ValueError("Use at least 25 decimal digits.")
    mp.mp.dps = dps
    C, c, scut = constants()
    cuts = [0, 2*mp.asin(1/C), 2*mp.asin(mp.sqrt(1/(scut*C))),
            mp.mpf('0.5'), mp.mpf('1.5'), mp.pi]
    J = mp.quad(log_density_angle, cuts)/mp.pi
    K = mp.pi*C/2*mp.exp(J)
    result = {'dps': dps,
              'status': 'numerical quadrature; not a rigorous decimal enclosure',
              'endpoint_angle_cutoff': '1e-8',
              'C': mp.nstr(C, 28), 'Lambda': mp.nstr(C/4, 28),
              'mean_log_phi': mp.nstr(J, 28), 'K': mp.nstr(K, 28),
              'OEIS_plot_limit': mp.nstr(K*C/4, 28),
              'linear_coefficient': mp.nstr(mp.log(C/4)+mp.log(K), 28),
              'inverse_offset': mp.nstr(-(mp.log(C/4)+mp.log(K))/(2*mp.log(C/4)), 28)}
    exact = [1,5,73,1445,33001]
    checks = []
    for k, target in enumerate(exact):
        def f(t):
            x = C*mp.sin(t/2)**2
            return mp.exp(log_density_angle(t))*x**k*C*mp.sin(t)/2
        value = mp.quad(f, cuts)
        checks.append({'k': k, 'value': mp.nstr(value, 28),
                       'absolute_error': mp.nstr(abs(value-target), 8)})
    result['moment_checks'] = checks
    return result

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--dps', type=int, default=40)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    text = json.dumps(evaluate(args.dps), indent=2)
    if args.output: args.output.write_text(text+'\n')
    else: print(text)
