#!/usr/bin/env python3
"""High-precision numerical illustrations of the proved two-frequency law.

The proof is analytic. These calculations are NOT interval certificates and do
not establish the theorem or the location of any zeta zero. Requires mpmath.
Run: python3 two_frequency.py --output two_frequency_data.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 90


def bisect_root(f, lo, hi, iterations=350):
    """Bisection with a strict sign change; both orientations are allowed."""
    flo, fhi = f(lo), f(hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if flo * fhi >= 0:
        raise ValueError("Root is not bracketed")
    for _ in range(iterations):
        mid = (lo + hi) / 2
        fm = f(mid)
        if fm == 0:
            return mid
        if fm * flo > 0:
            lo, flo = mid, fm
        else:
            hi, fhi = mid, fm
    return (lo + hi) / 2


def optimal_filter(r):
    r = mp.mpf(r)
    if r <= 1:
        raise ValueError("The independent-frequency problem requires r > 1")
    if r == mp.floor(r) and int(r) % 2:
        return dict(r=r, H=mp.pi/2, a=mp.pi/2, M=None,
                    alpha=mp.mpf(0), beta=mp.mpf(1),
                    locations=[-mp.pi/2, mp.pi/2],
                    weights=[mp.mpf('0.5')]*2, odd=True)
    k = int(mp.floor((r + 1) / 2))
    sign = (-1) ** k
    if k == 1:
        a, M, H = mp.mpf(0), mp.mpf(1), 2*mp.pi/(1+r)
    else:
        def tangent(t):
            u = r*t - (k-1)*mp.pi
            return r*mp.sin(u)*mp.cos(t)-mp.cos(u)*mp.sin(t)
        a = bisect_root(tangent, (k-1)*mp.pi/r, (mp.mpf(k)-mp.mpf('0.5'))*mp.pi/r)
        M = -sign*mp.cos(r*a)/mp.cos(a)
        q = lambda t: sign*mp.cos(r*t)+M*mp.cos(t)
        H = bisect_root(q, mp.pi/2, min(mp.pi, (mp.mpf(k)+mp.mpf('0.5'))*mp.pi/r))
    alpha = -mp.cos(H)/(mp.cos(a)-mp.cos(H))
    beta = mp.cos(a)/(mp.cos(a)-mp.cos(H))
    if a == 0:
        locations, weights = [-H, a, H], [beta/2, alpha, beta/2]
    else:
        locations, weights = [-H, -a, a, H], [beta/2, alpha/2, alpha/2, beta/2]
    return dict(r=r, H=H, a=a, M=M, alpha=alpha, beta=beta,
                locations=locations, weights=weights, odd=False, sign=sign)


def phi(data, w):
    return sum(weight*mp.exp(1j*w*t) for t, weight in zip(data['locations'], data['weights']))


def check(data):
    residual = max(abs(phi(data, 1)), abs(phi(data, data['r'])))
    assert residual < mp.mpf('1e-75'), residual
    assert abs(sum(data['weights'])-1) < mp.mpf('1e-75')
    assert min(data['weights']) > 0
    if not data['odd']:
        grid_min = min(data['sign']*mp.cos(data['r']*data['H']*j/500)
                       + data['M']*mp.cos(data['H']*j/500)
                       for j in range(501))
        assert grid_min > -mp.mpf('1e-75'), grid_min
    else:
        grid_min = mp.mpf(0)
    return dict(max_fourier_residual=residual, sampled_dual_minimum=grid_min)


def serialize(value):
    if isinstance(value, dict):
        return {k: serialize(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serialize(x) for x in value]
    if isinstance(value, (str, int, bool)) or value is None:
        return value
    return mp.nstr(value, 50)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='two_frequency_data.json')
    args = parser.parse_args()
    cases = []
    for r in ['1.000001', '1.5', '2', '2.999999', '3', '3.000001',
              '3.01', '3.5', '4', '4.5', '4.999999', '5', '5.000001',
              '6', '7', '7.000001', '8', '9', '9.000001', '10', '15.2']:
        data = optimal_filter(r)
        data.update(check(data))
        cases.append(data)
    cusps = []
    for m in [3, 5, 7, 9]:
        C = (3*mp.pi/(2*m*(m*m-1))) ** (mp.mpf(1)/3)
        for power in [3, 6, 9, 12, 18]:
            eps = mp.mpf(10) ** -power
            data = optimal_filter(m+eps)
            check(data)
            u, v = mp.pi/2-data['a'], data['H']-mp.pi/2
            cusps.append(dict(m=m, epsilon=eps,
                u_over_predicted=u/(C*eps**(mp.mpf(1)/3)),
                v_over_predicted=v/(2*C*eps**(mp.mpf(1)/3)),
                v_over_u=v/u, inner_pair_mass=data['alpha'],
                outer_pair_mass=data['beta']))
    # Numerical illustration; zero locations here are NOT certified by this code.
    g1, g2 = mp.im(mp.zetazero(1)), mp.im(mp.zetazero(2))
    z = optimal_filter(g2/g1)
    check(z)
    zeta = dict(first_ordinate=g1, second_ordinate=g2, ratio=g2/g1,
                half_width=z['H']/g1, diameter=2*z['H']/g1,
                scale_ratio=mp.exp(2*z['H']/g1),
                log_scales=[x/g1 for x in z['locations']], weights=z['weights'])
    result = dict(status='Numerical illustrations, not interval certificates',
                  decimal_precision=mp.mp.dps, cases=cases,
                  right_cusp_checks=cusps, zeta_first_two=zeta)
    Path(args.output).write_text(json.dumps(serialize(result), indent=2)+'\n')
    print(json.dumps(dict(status='all checks passed', cases=len(cases),
                         cusp_checks=len(cusps), output=str(Path(args.output).resolve())), indent=2))


if __name__ == '__main__':
    main()
