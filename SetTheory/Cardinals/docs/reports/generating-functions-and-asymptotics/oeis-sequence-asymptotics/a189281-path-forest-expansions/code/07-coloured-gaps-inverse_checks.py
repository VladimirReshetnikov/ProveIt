#!/usr/bin/env python3
"""Exact inverse algebra plus explicitly labeled floating model diagnostics.
Requires SymPy and mpmath. Output is JSON on stdout; logs go to stderr.
Never writes files. All guards remain enabled with python -O.
"""
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
"""Exact symbolic and independent numerical checks for colored-gap inverses.

Run: python check_inverses.py
Dependencies already available in the execution environment: sympy, mpmath.
No network, saved coefficients, candidate modules, or external services are used.
The numerical checks DO NOT certify a counting-sequence asymptotic onset.
"""
from itertools import permutations
import json
import mpmath as mp
import sympy as sp

def algebra():
    L, t, b1, b2 = sp.symbols('L t b1 b2', nonzero=True)
    B = b1 + (t * t - t) / 2
    u0 = -t
    u1 = -B / L
    u2 = -(b2 + b1 * t + t ** 3 / 6 - t ** 2 / 4 + (t - sp.Rational(1, 2)) * B / L) / L
    residuals = [L * u0 + L * t, L * u1 + (u0 * u0 + u0) / 2 + b1, L * u2 + (u0 + sp.Rational(1, 2)) * u1 - u0 ** 3 / 6 - u0 * u0 / 4 - b1 * u0 + b2]
    if not all((sp.cancel(r) == 0 for r in residuals)):
        raise ValueError('Inverse check failed')
    z = sp.symbols('z')
    delta = u0 + u1 * z + u2 * z * z
    H = L * (delta + t) + delta ** 2 * z / 2 - delta ** 3 * z * z / 6 + sp.log(1 + z * delta) / 2 + b1 * z / (1 + z * delta) + b2 * z * z / (1 + z * delta) ** 2
    trunc = sp.series(H, z, 0, 3).removeO().expand()
    if not all((sp.cancel(trunc.coeff(z, j)) == 0 for j in range(3))):
        raise ValueError('Inverse check failed')
    beta = [None, sp.Rational(97, 12), sp.Integer(16), sp.Rational(7, 3), sp.Rational(-5, 7)]
    u = [-t]
    for j in range(1, 5):
        d = sum((u[i] * z ** i for i in range(j)))
        H = L * (d + t)
        H += sum(((-1) ** r * d ** r * z ** (r - 1) / sp.Integer(r * (r - 1)) for r in range(2, j + 2)))
        H += sum(((-1) ** (r + 1) * (z * d) ** r / sp.Integer(2 * r) for r in range(1, j + 1)))
        H += sum((beta[k] * z ** k * sum(((-1) ** r * sp.binomial(k + r - 1, r) * (z * d) ** r for r in range(j - k + 1))) for k in range(1, j + 1)))
        R = sp.expand(H).coeff(z, j)
        u.append(sp.cancel(-R / L))
        if not sp.cancel(L * u[-1] + R) == 0:
            raise ValueError('Inverse check failed')
    c1, c2, c3 = sp.symbols('c1 c2 c3')
    qlog = sp.series(sp.log(1 + c1 * z + c2 * z * z + c3 * z ** 3), z, 0, 4).removeO().expand()
    if not sp.expand(qlog.coeff(z, 1) - c1) == 0:
        raise ValueError('Inverse check failed')
    if not sp.expand(qlog.coeff(z, 2) - (c2 - c1 * c1 / 2)) == 0:
        raise ValueError('Inverse check failed')
    if not sp.expand(qlog.coeff(z, 3) - (c3 - c1 * c2 + c1 ** 3 / 3)) == 0:
        raise ValueError('Inverse check failed')
    ratio = sp.series((1 + 8 * z + 48 * z * z) / (1 + 4 * z + 28 * z * z), z, 0, 3).removeO()
    if not sp.expand(ratio - (1 + 4 * z + 4 * z * z)) == 0:
        raise ValueError('Inverse check failed')
    endpoint_margin = sp.Rational(1, 2) - sp.Rational(97, 12 * 31) - sp.Rational(48, 31 ** 2)
    if not endpoint_margin > 0:
        raise ValueError('Inverse check failed')
    curvature_factor = sp.Rational(32, 31) * (1 + sp.Rational(16, 31 ** 2) + sp.Rational(288, 31 ** 3))
    if not curvature_factor < 2:
        raise ValueError('Inverse check failed')
    print('PASS: exact u0,u1,u2 residuals, independent direct series, and order-4 recurrence fixture')
    print('PASS: logarithmic coefficients, camel/knight quotient, and exact endpoint/curvature margins')
    print('endpoint margin =', endpoint_margin, '; curvature upper factor =', curvature_factor)
    return {'explicit_residuals_zero': True, 'recurrence_fixture_order': 4, 'endpoint_margin': str(endpoint_margin), 'curvature_upper_factor': str(curvature_factor)}

def numerical():
    mp.mp.dps = 100
    fixtures = []
    print('\nFinite quadratic-model tests (100 decimal digits; these are not sequence-onset certificates):')
    print('model  X  root h2  Newton errors after 1,2,3 steps  scaled explicit-centre error')
    for name, a, b in [('camel', 8, 48), ('knight', 4, 28)]:
        for integer_X in [32, 100, 1000, 10 ** 6]:
            X = mp.mpf(integer_X)
            L = mp.log(X)
            logy = X * (L - 1) - 4
            S = logy + 4
            seed = S / mp.lambertw(S / mp.e)
            if not abs(seed - X) < mp.mpf('1e-90') * X:
                raise ValueError('Inverse check failed')

            def F(x):
                return mp.loggamma(x + 1) - 4 + mp.log1p(a / x + b / x ** 2)

            def DF(x):
                return mp.digamma(x + 1) - (a / x ** 2 + 2 * b / x ** 3) / (1 + a / x + b / x ** 2)
            h = mp.findroot(lambda x: F(x) - logy, (X - 1, X), solver='secant', tol=mp.mpf('1e-95'))
            if not X - 1 < h < X:
                raise ValueError('Inverse check failed')
            v = X
            errors = []
            for j in range(1, 4):
                v -= (F(v) - logy) / DF(v)
                err = v - h
                bound = (2 / (X * L)) ** (2 ** j - 1)
                if not 0 <= err <= bound:
                    raise ValueError('Inverse check failed')
                errors.append(mp.nstr(err, 14))
            t = mp.log(2 * mp.pi * X) / (2 * L)
            b1 = a + mp.mpf(1) / 12
            b2 = b - mp.mpf(a) ** 2 / 2
            B = b1 + (t * t - t) / 2
            centre = X - t - B / (X * L) - (b2 + b1 * t + t ** 3 / 6 - t * t / 4 + (t - mp.mpf('0.5')) * B / L) / (X ** 2 * L)
            scaled = (centre - h) * X ** 3 * L
            print(name, integer_X, mp.nstr(h, 18), ' '.join(errors), mp.nstr(scaled, 14))
            fixtures.append({'model': name, 'X': integer_X, 'log_y': mp.nstr(logy, 40), 'root_h2': mp.nstr(h, 50), 'newton_errors': errors, 'explicit_centre': mp.nstr(centre, 50), 'scaled_centre_error': mp.nstr(scaled, 25)})
    print('PASS: all finite-model roots, Lambert identities, monotone Newton iterates, and analytic error bounds')
    return fixtures

def small_counts():
    expected = {2: [1, 1, 2, 2, 8, 20, 94, 438, 2766, 19480], 3: [1, 1, 2, 6, 8, 24, 126, 524, 3072, 22854]}
    results = {}
    for R in (2, 3):
        counts = []
        for n in range(10):
            total = 0
            for p in permutations(range(n)):
                if all((abs(p[i + 1] - p[i]) != R for i in range(n - 1))) and all((abs(p[i + R] - p[i]) != 1 for i in range(n - R))):
                    total += 1
            counts.append(total)
        if not counts == expected[R]:
            raise ValueError((R, counts))
        results[str(R)] = counts
        print('PASS: independent direct permutations R=' + str(R) + ', n=0,...,9:', counts)
    print('The knight plateau a2=a3=2 confirms that only eventual strict monotonicity was asserted.')
    return results

def exact_and_numeric_json():
    import contextlib
    with contextlib.redirect_stdout(sys.stderr):
        result = {'algebra': algebra(), 'quadratic_model_fixtures': numerical(),
                  'small_counts': small_counts(),
                  'limits': ['No actual sequence remainder constant or onset certified.',
                             'Quadratic model coefficients above order two are not sequence coefficients.',
                             'Numerical high-precision tests supplement, not replace, the proofs.']}
    return json.dumps(result, sort_keys=True, indent=2) + '\n'

if __name__ == '__main__':
    if len(sys.argv) != 1:
        raise ValueError('This checker takes no arguments; use build.py')
    sys.stdout.write(exact_and_numeric_json())

