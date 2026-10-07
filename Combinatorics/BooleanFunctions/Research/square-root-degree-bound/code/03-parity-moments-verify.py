#!/usr/bin/env python3
"""Independent finite arithmetic and numerical diagnostics for the article.

Exact checks use Fraction and polynomial arithmetic from the standard library.
The mpmath diagnostics are optional and are not mathematical certificates.
Run from the package root: python3 code/verify.py --numerical
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parity(x):
    return 1 if x % 2 == 0 else -1


def polynomial_product_roots(nodes):
    coeff = [1]
    for x in nodes:
        new = [0] * (len(coeff) + 1)
        for i, c in enumerate(coeff):
            new[i] -= x * c
            new[i + 1] += c
        coeff = new
    return coeff


def eval_poly(coeff, x):
    value = 0
    for c in reversed(coeff):
        value = value * x + c
    return value


def weights(nodes):
    """Use derivatives of the expanded node polynomial, not pair products."""
    coeff = polynomial_product_roots(nodes)
    derivative = [i * coeff[i] for i in range(1, len(coeff))]
    raw = [F(1, abs(eval_poly(derivative, x))) for x in nodes]
    total = sum(raw)
    return [w / total for w in raw]


def moments(nodes, probs, degree):
    ordinary = [sum(p * x**j for x, p in zip(nodes, probs))
                for j in range(degree + 1)]
    signed = [sum(parity(x) * p * x**j for x, p in zip(nodes, probs))
              for j in range(degree + 1)]
    return ordinary, signed


def affine_nodes(k, radius):
    require(k >= 3 and radius >= 18 and radius % 2 == 0, 'parameters')
    xs = [0, 1, 2, 3]
    z = radius
    for _ in range(k - 3):
        xs.append(z)
        z = 3 * z + 1
    return xs


def qpoch_exact(a, q, n):
    result = F(1)
    for _ in range(n):
        result *= 1 - a
        a *= q
    return result


def affine_product_weights(k, radius):
    """Separate finite q-product formula for rescaled unnormalized weights."""
    count = k - 3
    q, b, A = F(1, 3), F(1, 2 * radius + 1), F(2 * radius + 1, 2)
    P = qpoch_exact(b, q, count)
    core = [P / (math.factorial(i) * math.factorial(3 - i)
                 * qpoch_exact((2 * i + 1) * b, q, count))
            for i in range(4)]
    tail = []
    for ell in range(count):
        denominator = qpoch_exact(q, q, ell) * qpoch_exact(q, q, count - 1 - ell)
        for c in (1, 3, 5, 7):
            denominator *= 1 - c * b * q**ell
        tail.append(A**-3 * q**(ell * (ell + 7) // 2) * P / denominator)
    raw = core + tail
    return [x / sum(raw) for x in raw]


def exact_families():
    rows = []
    equations = 0
    for k in range(3, 19):
        for radius in (18, 32, 100, 1000):
            xs = affine_nodes(k, radius)
            ps = weights(xs)
            require(len(xs) == k + 1 and all(p > 0 for p in ps), 'positive support')
            require(all(x % 2 == i % 2 for i, x in enumerate(xs)), 'parity order')
            ms, sm = moments(xs, ps, k)
            require(ms[0] == 1, 'normalization')
            require(all(x == 0 for x in sm[:k]), f'moment equations {k} {radius}')
            require(sm[k] != 0, 'first uncancelled moment')
            variance = ms[2] - ms[1]**2
            require(variance >= F(3, 4), 'lattice lower bound')
            require(variance <= F(3, 4) + F(12, radius), 'uniform upper bound')
            if k >= 4:
                require(variance > F(3, 4), 'nonattainment')
            require(ps == affine_product_weights(k, radius), 'q-product weights')
            equations += k
            rows.append({'k': k, 'R': radius, 'atoms': len(xs),
                         'max_support': str(xs[-1]),
                         'variance': str(variance), 'variance_decimal': float(variance),
                         'R_times_excess': float(radius * (variance - F(3, 4)))})
    return {'families': len(rows), 'signed_equations': equations, 'rows': rows}


def fixed_mean_checks():
    results = []
    for u in (F(0), F(1, 10), F(1, 4), F(2, 5), F(49, 100)):
        threshold = (2 - u) / (2 - 4 * u)
        a = (threshold.numerator + threshold.denominator - 1) // threshold.denominator

        def even_law(depth):
            pminus = (1 - 2 * u) / (4 * depth * (depth + 1))
            pplus = (1 + 2 * depth * u) / (4 * (depth + 1))
            return {-2 * depth: pminus, 0: 1 - pminus - pplus, 2: pplus}

        theta = F(0) if u == 0 else 3 * u / (2 * (a - 1) * (1 - 2 * u))
        require(0 <= theta <= 1, 'mixture coefficient')
        joint = {-1: (1 - u) / 4, 1: (1 + u) / 4}
        for mass, law in ((1 - theta, even_law(1)), (theta, even_law(a))):
            for x, p in law.items():
                joint[x] = joint.get(x, F(0)) + mass * p / 2
        xs, ps = list(joint), list(joint.values())
        ms, sm = moments(xs, ps, 4)
        require(ms[0] == 1 and ms[1] == u and ms[2] == 1, 'fixed mean moments')
        require(all(v == 0 for v in sm[:4]), 'fourth order equality law')
        require(sm[4] != 0, 'fifth order obstruction')
        require(all(p >= 0 for p in ps), 'positive fixed mean law')
        if a > 1:
            require(2 * (a - 1) - 2 - (4 * (a - 1) - 1) * u < 0,
                    'previous depth infeasible')
        results.append({'u': str(u), 'a': a, 'theta': str(theta),
                        'variance': str(1 - u**2),
                        'law': {str(x): str(p) for x, p in sorted(joint.items()) if p}})
    return results


def numerical_checks():
    import mpmath as mp
    mp.mp.dps = 100
    R = 32
    q = mp.mpf(1) / 3
    b, A = mp.mpf(1) / (2 * R + 1), mp.mpf(R) + mp.mpf('0.5')
    P, Q = mp.qp(b, q), mp.qp(q, q)
    core = [P / (mp.factorial(i) * mp.factorial(3 - i) * mp.qp((2*i+1)*b, q))
            for i in range(4)]
    count = 150
    zs = [A * 3**ell - mp.mpf('0.5') for ell in range(count)]
    us = [A**-3 * q**(ell*(ell+7)//2) * P /
          (mp.qp(q, q, ell) * Q * mp.fprod(1-c*b*q**ell for c in (1, 3, 5, 7)))
          for ell in range(count)]
    Z = sum(core) + sum(us)
    C = P / (Z * Q**2)

    def theta(a):
        middle = int(mp.floor(a))
        return mp.fsum(mp.power(3, -mp.mpf('0.5')*(ell-a)**2)
                       for ell in range(middle-25, middle+26))

    def coeffs(s, order):
        out = [mp.mpf(1)]
        for j in range(1, order+1):
            out.append(sum(((sum(c**r for c in (1, 3, 5, 7))-s)*b**r
                            - mp.mpf(1)/(3**r-1))*out[j-r]
                           for r in range(1, j+1)) / j)
        return out

    rows = []
    for s in [mp.mpf(v) for v in (8, 12, 20, 30, 40, '12.25', '20.5', '30.75')]:
        moment = (sum(core[i]*mp.mpf(i)**s for i in range(1, 4))
                  + mp.fsum(w*z**s for w, z in zip(us, zs))) / Z
        lead = C * A**(s-3) * mp.power(3, (s-mp.mpf('3.5'))**2/2) * theta(s-mp.mpf('3.5'))
        ratio = moment/lead
        coefficients = coeffs(s, 3)
        approximants = [sum(coefficients[j]*mp.power(3, -j*s+mp.mpf(j*(j+7))/2)
                            for j in range(order+1)) for order in range(4)]
        rows.append({'s': str(s), 'moment_log10': mp.nstr(mp.log10(moment), 30),
                     'normalized_moment': mp.nstr(ratio, 45),
                     'relative_errors_orders_0_to_3': [mp.nstr((v-ratio)/ratio, 15)
                                                       for v in approximants]})
    residuals = []
    for j in range(16):
        numerator = sum(parity(i)*core[i]*mp.mpf(i)**j for i in range(4))
        numerator += mp.fsum(parity(int(z))*w*z**j for z, w in zip(zs, us))
        denominator = sum(core[i]*mp.mpf(i)**j for i in range(4))
        denominator += mp.fsum(w*z**j for z, w in zip(zs, us))
        residuals.append(mp.nstr(abs(numerator)/denominator, 8))
    return {'kind': 'non-rigorous 100-digit diagnostics; exact finite checks are separate',
            'R': R, 'tail_terms': count, 'normalization': mp.nstr(Z, 45),
            'normalized_signed_residuals_j0_to15': residuals,
            'moment_expansion': rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--numerical', action='store_true')
    args = parser.parse_args()
    result = {'status': 'PASS', 'exact_affine_families': exact_families(),
              'fixed_mean_fourth_order': fixed_mean_checks()}
    if args.numerical:
        result['numerical_diagnostics'] = numerical_checks()
    (ROOT/'data').mkdir(exist_ok=True)
    destination = ROOT/'data'/'verification_results.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'],
                      'exact_families': result['exact_affine_families']['families'],
                      'exact_signed_equations': result['exact_affine_families']['signed_equations'],
                      'fixed_mean_examples': len(result['fixed_mean_fourth_order']),
                      'numerical_diagnostics': args.numerical,
                      'output': str(destination)}, indent=2))


if __name__ == '__main__':
    main()
