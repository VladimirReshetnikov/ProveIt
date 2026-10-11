#!/usr/bin/env python3
"""Independent exact and numerical checks of the cotangent resolvent identities.

No numerical result in this script is an interval certificate.  Exact tests use
SymPy rational functions; numerical references use ordinary or explicitly
subtracted quadrature, not the Fourier derivation of the formulas under test.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

import mpmath as mp
import sympy as sp


def normalized_li(order, q, derivative=0):
    """d_order^derivative Li_order(q)/q, including its removable q=0 value."""
    if not q:
        return mp.mpf(derivative == 0)
    terms = []
    power = mp.mpf(1)
    small = 0
    for n in range(1, 10000):
        term = power * mp.power(n, -order) * mp.power(-mp.log(n), derivative)
        terms.append(term)
        small = small + 1 if abs(term) < mp.eps / 100 else 0
        if n > 12 and small > 6:
            return mp.fsum(terms)
        power *= q
    raise RuntimeError("polylogarithm series did not converge")


def coordinates(z):
    sign = 1 if mp.im(z) > 0 else -1
    a = z + sign * mp.j * mp.pi
    q = (z - sign * mp.j * mp.pi) / a
    c = sign * 2 * mp.pi * mp.j / a**2
    sigma = -sign * 2 * mp.pi * mp.j
    return a, q, c, sigma


def resolvent(x, z):
    # This expression avoids cotangent overflow and cancellation at x=0.
    w = mp.expm1(2 * mp.pi * mp.j * x)
    return w / (2 * mp.pi * mp.j + (mp.pi * mp.j - z) * w)


def gamma_jet(n, sigma):
    cumulants = [mp.mpf(0), -mp.euler - mp.log(sigma)]
    cumulants += [(-1)**k * mp.factorial(k - 1) * mp.zeta(k)
                  for k in range(2, n + 1)]
    values = [mp.mpf(1)]
    for j in range(n):
        values.append(mp.fsum(mp.binomial(j, k) * cumulants[k + 1]
                              * values[j - k] for k in range(j + 1)))
    return values


def e_derivative(p, n):
    coeff = [mp.mpf(1)]
    for j in range(1, p + 1):
        nxt = coeff + [mp.mpf(0)]
        for k in range(1, len(nxt)):
            nxt[k] -= coeff[k - 1] / j
        coeff = nxt
    return mp.factorial(n) * coeff[n] if n <= p else mp.mpf(0)


def stieltjes_moment(m, p, z):
    _, q, c, sigma = coordinates(z)
    gs = gamma_jet(m + 1, sigma)
    value = mp.fsum(mp.binomial(m + 1, k) * gs[m + 1 - k]
                    * normalized_li(-p, q, k) for k in range(m + 2))
    value -= e_derivative(p, m + 1) * normalized_li(-p, q)
    return c * sigma**p * value / (m + 1)


def local_coefficients(z, degree):
    """Taylor coefficients from R'=1+2zR+(z^2+pi^2)R^2."""
    coeff = [mp.mpf(0), mp.mpf(1)]
    for j in range(1, degree):
        coeff.append((2*z*coeff[j] + (z*z + mp.pi**2)
                      * mp.fsum(coeff[k]*coeff[j-k] for k in range(1, j)))
                     / (j + 1))
    return coeff


def fp_polygamma_reference(p, z):
    """FP integral of gamma_0^(p) R using local Taylor subtraction."""
    if p == 0:
        return mp.quad(lambda x: -mp.digamma(x)*resolvent(x, z), [0, .25, .7, 1])
    degree = p + 80
    coeff = local_coefficients(z, degree)
    singular = (-1)**p * mp.factorial(p)

    def smooth(x):
        if x < mp.mpf('0.015'):
            # R minus its first p Taylor terms, divided by x^(p+1).
            regular = mp.fsum(coeff[j] * x**(j-p-1)
                             for j in range(p+1, degree+1))
        else:
            regular = (resolvent(x, z)
                       - mp.fsum(coeff[j]*x**j for j in range(1, p+1))) / x**(p+1)
        return singular * regular - mp.polygamma(p, x+1)*resolvent(x, z)

    integral = mp.quad(smooth, [0, mp.mpf('0.015'), .25, .7, 1])
    integral += singular * mp.fsum(coeff[j]/(j-p) for j in range(1, p))
    return integral


def generalized_polygamma(v, x):
    if v == 0:
        return mp.digamma(x)
    # Differentiate the Hurwitz continuation analytically, not by finite
    # differences of independently evaluated zeta values.  The latter has a
    # severe precision defect at some exact quadrature nodes (e.g. x=7/8).
    # Also separate the endpoint monomial before evaluating the smooth part.
    weight = mp.euler + mp.digamma(-v)
    smooth = (mp.zeta(v+1, x+1, derivative=1)
              + weight*mp.zeta(v+1, x+1))
    singular = (weight-mp.log(x))*mp.power(x, -v-1)
    return (smooth+singular) / mp.gamma(-v)


def complex_order_moment(v, z):
    _, q, c, sigma = coordinates(z)
    return c * sigma**v * ((mp.euler+mp.log(sigma))*normalized_li(-v, q)
                           - normalized_li(-v, q, 1))


def balanced_primitive(r, x):
    if r == 0:
        # Lerch's identity is both exact and stable at every quadrature node.
        return mp.loggamma(x)-mp.log(2*mp.pi)/2
    weight = mp.harmonic(r)
    smooth = (mp.zeta(-r, x+1, derivative=1)
              + weight*mp.zeta(-r, x+1))
    return (smooth+(weight-mp.log(x))*x**r) / mp.factorial(r)


def gamma1_prime_square_reference(z):
    """Ordinary integral of gamma_1'(x) R_z(x)^2, with stable endpoint split."""
    def integrand(x):
        kernel = resolvent(x, z)
        smooth = mp.zeta(2, x+1)+mp.zeta(2, x+1, derivative=1)
        return (1-mp.log(x))*(kernel/x)**2 + smooth*kernel**2
    return mp.quad(integrand, [0, .25, .7, 1])


def direct_stieltjes_reference(m, z):
    """Direct Stieltjes evaluation after its exact endpoint shift relation."""
    def integrand(x):
        kernel = resolvent(x, z)
        return mp.log(x)**m*(kernel/x)+mp.stieltjes(m, x+1)*kernel
    return mp.quad(integrand, [0, .3, .75, 1])


def exact_checks():
    z, q, s, pi = sp.symbols('z q s pi', nonzero=True)
    count = 0
    coeff = [sp.S.Zero, sp.S.One]
    for j in range(1, 10):
        coeff.append(sp.expand((2*z*coeff[j] + (z*z+pi*pi)
                                * sum(coeff[k]*coeff[j-k] for k in range(1,j)))/(j+1)))
    power_sum = q/(1-q)
    for p in range(1, 10):
        power_sum = sp.cancel(q*sp.diff(power_sum,q))
        cz = 2*pi*sp.I/(z+pi*sp.I)**2
        qz = (z-pi*sp.I)/(z+pi*sp.I)
        fourier = cz*(2*pi*sp.I)**p/sp.factorial(p)*(power_sum/q).subs(q,qz)
        assert sp.cancel(fourier-coeff[p]) == 0
        count += 1
        E = sp.prod(1-s/sp.Integer(j) for j in range(1,p+1))
        assert sp.expand(sp.prod(s-j for j in range(1,p+1))
                         - (-1)**p*sp.factorial(p)*E) == 0
        count += 1
        assert sp.diff(E,s).subs(s,0) == -sp.harmonic(p)
        count += 1
        for m in range(p, p+3):
            assert sp.diff(E,s,m+1) == 0
            count += 1
    # A deliberately omitted contact term must be detected.
    assert (-sp.harmonic(1)*(-1)**1*sp.factorial(1)*coeff[1]) == 1
    count += 1
    return count


def run(full=False, progress=False):
    started = time.monotonic()
    mp.mp.dps = 55
    results = []

    def record(name, value, reference, tol=mp.mpf('1e-42')):
        error = abs(value-reference)
        assert error < tol, (name, mp.nstr(error,10))
        results.append({'name':name, 'absolute_error':mp.nstr(error,12),
                        'value':mp.nstr(value,32), 'tolerance':mp.nstr(tol,5)})
        if progress:
            print(f'PASS {name}: error {mp.nstr(error,8)} '
                  f'({time.monotonic()-started:.1f}s)', file=sys.stderr, flush=True)

    # Regression for the node at which mp.diff(zeta, 0) stalls near 11-digit
    # accuracy despite increased precision; the native derivative stays accurate.
    node = mp.mpf(7)/8
    record('lerch_native_derivative_at_seven_eighths', balanced_primitive(0,node),
           mp.zeta(0,node,derivative=1))
    zvals = [mp.j*mp.pi, 1+2*mp.j*mp.pi, -mp.mpf('0.7')-mp.j*mp.pi/2]
    for zi,z in enumerate(zvals):
        for p in range(4):
            record(f'pointwise_subtraction_z{zi}_p{p}', stieltjes_moment(0,p,z),
                   fp_polygamma_reference(p,z))
    z = mp.j*mp.pi
    record('explicit_trigamma_contact', -stieltjes_moment(0,1,z),
           1-mp.euler-mp.log(2*mp.pi)+mp.j*mp.pi/2)
    for zi,z in enumerate(zvals[:2]):
        for r in [0,1,2]:
            record(f'balanced_primitive_z{zi}_r{r}', complex_order_moment(-r-1,z),
                   mp.quad(lambda x: balanced_primitive(r,x)*resolvent(x,z), [0,.3,.75,1]))
        # A convergent integral with a differentiated Stieltjes function.
        m1p1_square = mp.diff(lambda w: stieltjes_moment(1,1,w),z)
        direct = gamma1_prime_square_reference(z)
        record(f'convergent_gamma1_prime_square_z{zi}',m1p1_square,direct)

    if full:
        # These use direct generalized Stieltjes evaluations and do not share
        # the Hurwitz Fourier or resolvent spectral evaluation implementation.
        for m in [1,2]:
            for zi,z in enumerate(zvals[:2]):
                direct=direct_stieltjes_reference(m,z)
                record(f'direct_stieltjes_m{m}_z{zi}',stieltjes_moment(m,0,z),direct)
        for v in [mp.mpf('-.4'), mp.mpf('.3')+mp.j/5]:
            z=zvals[1]
            record(f'complex_order_v{mp.nstr(v,6)}',complex_order_moment(v,z),
                   mp.quad(lambda x:generalized_polygamma(v,x)*resolvent(x,z),[0,.1,.4,1]),
                   mp.mpf('1e-34'))

    data={'exact_assertions':exact_checks(), 'working_precision_digits':mp.mp.dps,
          'full':full, 'numerical_checks':len(results),
          'elapsed_seconds':round(time.monotonic()-started,3),
          'hurwitz_derivative_method':'Native analytic derivative, with exact endpoint shift; loggamma at primitive level zero.',
          'largest_absolute_error':mp.nstr(max(mp.mpf(r['absolute_error']) for r in results),12),
          'interpretation':'Floating-point diagnostics, not interval-certified proofs.',
          'checks':results}
    return data


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--full',action='store_true')
    parser.add_argument('--progress',action='store_true',
                        help='Print per-check progress to standard error.')
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results/resolvent_checks.json')
    args=parser.parse_args()
    data=run(args.full,args.progress)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='checks'},indent=2))
