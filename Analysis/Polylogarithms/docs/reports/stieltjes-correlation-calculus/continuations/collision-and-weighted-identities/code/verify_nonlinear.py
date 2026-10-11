#!/usr/bin/env python3
"""Exact endpoint-coordinate checks, plus independent finite-part quadrature.

The exact checks compare the distribution coefficient formula with constants
of elementary antiderivatives under nonlinear substitutions. The test germs
f'(x) f(x)^j form a triangular basis of the necessary test-function jets.
This is a reproducibility check for the proved theorem, not a proof assistant
formalization. Requires sympy and mpmath.
"""
from pathlib import Path
from functools import lru_cache
import json
import time
import sympy as s
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
x, z, L = s.symbols('x z L')


def trunc(expr, degree):
    return s.Add(*[
        c*x**k[0] for k, c in s.Poly(s.expand(expr), x).terms()
        if k[0] <= degree])


@lru_cache(maxsize=None)
def hpower(f, exponent, degree):
    """Taylor polynomial of (f/x)^exponent, with the scale exponential apart."""
    p = s.expand(f).coeff(x, 1)
    v = s.expand(f/(p*x)-1)
    total, vk, bk = s.Integer(1), s.Integer(1), s.Integer(1)
    for k in range(1, degree+1):
        vk = trunc(vk*v, degree)
        bk = s.expand(bk*(exponent-k+1)/k)
        total += bk*vk
    return s.expand(total)


def zexp_coeff(poly, n):
    poly = s.Poly(s.expand(poly), z)
    return s.expand(sum(poly.nth(k)*L**(n-k)/s.factorial(n-k)
                        for k in range(n+1)))


def coordinate_defect(f, q, n):
    p = s.expand(f).coeff(x, 1)
    hp = hpower(f, z-q, q-1)
    return [s.expand(s.factorial(n)*(-1)**j/s.factorial(j)/p**q
                     * zexp_coeff(hp.coeff(x, q-1-j), n+1))
            for j in range(q)]


def stieltjes_contact(f, n, r):
    p = s.expand(f).coeff(x, 1)
    er = s.prod(1-z/s.Integer(h) for h in range(1, r+1))
    hp = hpower(f, z-r-1, r)
    return [s.expand(s.factorial(n)*s.factorial(r)*(-1)**(r+j)
                     /s.factorial(j)/p**(r+1)
                     *zexp_coeff(er*hp.coeff(x, r-j), n+1))
            for j in range(r+1)]


def pair_jet(distribution, phi):
    phi = s.expand(phi)
    return s.expand(sum(c*(-1)**j*s.factorial(j)*phi.coeff(x, j)
                        for j, c in enumerate(distribution)))


def primitive_cutoff_constant(f, q, n, j):
    """Independent CT of an elementary primitive of y^(j-q) log(y)^n."""
    p = s.expand(f).coeff(x, 1)
    a = 1+j-q
    if a == 0:
        return L**(n+1)/s.Integer(n+1)
    degree = -a
    v = s.expand(f/(p*x)-1)
    logh = sum((-1)**(k+1)*trunc(v**k, degree)/s.Integer(k)
               for k in range(1, degree+1))
    power = hpower(f, s.Integer(a), degree)
    primitive = sum((-1)**k*s.factorial(n)/s.factorial(n-k)
                    *trunc((L+logh)**(n-k), degree)/s.Integer(a)**(k+1)
                    for k in range(n+1))
    return s.expand(p**a*trunc(power*primitive, degree)).coeff(x, degree)


def pullback_delta(g, r):
    p = s.expand(g).coeff(x, 1)
    hp = hpower(g, -s.Integer(r)-1, r)/p**(r+1)
    return [s.expand((-1)**(r-j)*s.factorial(r)/s.factorial(j)
                     *hp.coeff(x, r-j)) for j in range(r+1)]


def singular_expansion_unit(f, q, n):
    """Expand u(f(x)) directly in powers x^(-l)*log(x)^m, tangent p=1."""
    ell = s.Symbol('ell')
    v = s.expand(f/x-1)
    logh = sum((-1)**(k+1)*trunc(v**k, q-1)/s.Integer(k)
               for k in range(1, q))
    numerator = trunc(hpower(f, -s.Integer(q), q-1)
                      *trunc((ell+logh)**n, q-1), q-1)
    return {(q-k, m): s.expand(numerator).coeff(x, k).coeff(ell, m)
            for k in range(q) for m in range(n+1)}


def run():
    started = time.time()
    exact = []
    maps = [x+x*x/3-x**3/7+2*x**4/9,
            2*x-x*x/5+3*x**3/7+x**4/11,
            3*x+2*x*x/7-x**3/13]
    for i, f in enumerate(maps):
        for q in range(1, 6):
            for n in range(4):
                defect = coordinate_defect(f, q, n)
                for j in range(q):
                    lhs = pair_jet(defect, s.diff(f, x)*f**j)
                    rhs = primitive_cutoff_constant(f, q, n, j)
                    residual = s.expand(lhs-rhs)
                    assert residual == 0, (i, q, n, j, residual)
                    exact.append({'kind': 'elementary_cutoff_comparison',
                                  'map': i, 'q': q, 'n': n, 'test_jet': j,
                                  'residual': '0'})
    for f, g in [(maps[0], x+2*x*x/5+x**3/7),
                 (x-x*x/3+x**3/5, maps[0])]:
        for q in range(1, 5):
            for n in range(3):
                fg = trunc(f.subs(x, g), q)
                lhs = [c.subs(L, 0) for c in coordinate_defect(fg, q, n)]
                rhs = [s.Integer(0)]*q
                cf = [c.subs(L, 0) for c in coordinate_defect(f, q, n)]
                for r, c in enumerate(cf):
                    for j, v in enumerate(pullback_delta(g, r)):
                        rhs[j] += c*v
                for (qq, nn), c in singular_expansion_unit(f, q, n).items():
                    if c == 0:
                        continue
                    for j, v in enumerate(coordinate_defect(g, qq, nn)):
                        rhs[j] += c*v.subs(L, 0)
                assert all(s.expand(a-b) == 0 for a, b in zip(lhs, rhs))
                exact.append({'kind': 'nonlinear_composition_cocycle',
                              'q': q, 'n': n, 'residual': '0'})
    a, b = s.symbols('a b')
    f = x+a*x*x+b*x**3
    examples = {
        (0, 1): [-3*a, -1],
        (1, 1): [a, 0],
        (0, 2): [11*b-25*a*a, -11*a, -s.Rational(3, 2)],
        (3, 2): [3*a*a, 0, 0],
    }
    for (n, r), expected in examples.items():
        got = [c.subs(L, 0) for c in stieltjes_contact(f, n, r)]
        assert all(s.expand(u-v) == 0 for u, v in zip(got, expected))
        exact.append({'kind': 'explicit_contact', 'n': n, 'r': r,
                      'coefficients': [str(v) for v in got], 'residual': '0'})
    # The top surviving term and all coefficients immediately above it.
    for r in range(1, 6):
        f = x+a*x*x+b*x**3
        got = [s.expand(c.subs(L, 0)) for c in stieltjes_contact(f, 2*r-1, r)]
        assert s.expand(got[0]-s.factorial(2*r-1)/s.factorial(r)*a**r) == 0
        assert all(c == 0 for c in got[1:])
        for n in [2*r, 2*r+1]:
            assert all(s.expand(c.subs(L, 0)) == 0
                       for c in stieltjes_contact(f, n, r))
        exact.append({'kind': 'sharp_unit_tangent_threshold', 'r': r,
                      'residual': '0'})
    mp.mp.dps = 70
    numerical = []
    # Subtract the local singular terms before quadrature. This uses only
    # polygamma functions and the proved primitive formulas as comparison.
    for cc, bb in [('0.3', '0.6'), ('-0.2', '0.7')]:
        c, b = mp.mpf(cc), mp.mpf(bb)
        B = b+c*b*b
        # (1+2cx)*psi'(x+cx^2) = x^-2 + (zeta(2)-c^2) + O(x)
        def regular1(t):
            if abs(t) < mp.mpf('1e-24'):
                return mp.zeta(2)-c*c
            return (1+2*c*t)*mp.polygamma(1, t+c*t*t)-1/t**2
        lhs = -1/b+mp.quad(regular1, [0, b/2, b])
        rhs = mp.digamma(B)+mp.euler-c
        err = abs(lhs-rhs)
        assert err < mp.mpf('1e-45'), err
        numerical.append({'kind': 'nonlinear_trigamma_primitive',
                          'c': cc, 'b': bb, 'lhs': mp.nstr(lhs, 60),
                          'rhs': mp.nstr(rhs, 60),
                          'absolute_error': mp.nstr(err, 10)})
        # derivative of psi'(f): -2*x^-3+2*c*x^-2+O(1).
        def regular2(t):
            if abs(t) < mp.mpf('1e-18'):
                return -4*c**3-2*mp.zeta(3)
            return ((1+2*c*t)*mp.polygamma(2, t+c*t*t)
                    +2/t**3-2*c/t**2)
        lhs = 1/b**2-2*c/b+mp.quad(regular2, [0, b/2, b])
        rhs = mp.polygamma(1, B)-mp.zeta(2)-3*c*c
        err = abs(lhs-rhs)
        assert err < mp.mpf('1e-32'), err
        numerical.append({'kind': 'nonlinear_second_polygamma_primitive',
                          'c': cc, 'b': bb, 'lhs': mp.nstr(lhs, 55),
                          'rhs': mp.nstr(rhs, 55),
                          'absolute_error': mp.nstr(err, 10)})
    report = {'exact_check_count': len(exact), 'numerical_check_count': len(numerical),
              'working_decimal_digits': mp.mp.dps,
              'max_numerical_absolute_error': max(float(v['absolute_error']) for v in numerical),
              'numerical_results_are_certified_intervals': False,
              'elapsed_seconds': time.time()-started,
              'exact_checks': exact, 'numerical_checks': numerical}
    out = ROOT/'results/nonlinear_checks.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('exact_checks', 'numerical_checks')}, indent=2))


if __name__ == '__main__':
    run()
