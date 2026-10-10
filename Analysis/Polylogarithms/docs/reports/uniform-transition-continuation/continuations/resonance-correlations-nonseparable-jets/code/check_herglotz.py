#!/usr/bin/env python3
"""Independent numerical checks for herglotz_fragment.tex.

Requires mpmath.  Floating-point checks supplement, and do not replace,
the analytic proofs.  Finite-r values use the defining Hurwitz-zeta sum
with an Euler--Maclaurin tail bound, independently of the proposed
gamma-concentration coefficients.  Bessel checks include an analytic
tail estimate.  Run: python check_herglotz.py [output.json]
"""
from __future__ import annotations

from functools import lru_cache
import json
from pathlib import Path
import sys

import mpmath as mp

mp.mp.dps = 75
PROFILE_N = 16
PROFILE_M = 48


def fmt(x, digits=45):
    return mp.nstr(x, digits)


def B(t):
    if not t:
        return mp.mpf('0.5')
    return -1 / mp.expm1(-t) - 1 / t


@lru_cache(None)
def berncoeff(m):
    return mp.bernoulli(2*m) / mp.factorial(2*m)


@lru_cache(None)
def profile_tail_zeta(s):
    return mp.zeta(s, PROFILE_N)


def profile(lam, derivative=0):
    """S and its derivatives, using a finite elementary sum + convergent tail."""
    terms = []
    for n in range(1, PROFILE_N):
        if derivative:
            term = mp.diff(lambda z: B(1/(n*z)), lam, derivative) / n**2
        else:
            term = B(1/(n*lam)) / n**2
        terms.append(term)
    if not derivative:
        terms.append(profile_tail_zeta(2)/2)
    for m in range(1, PROFILE_M+1):
        alpha = 2*m-1
        terms.append(berncoeff(m) * profile_tail_zeta(2*m+1)
                     * (-1)**derivative * mp.rf(alpha, derivative)
                     * lam**(-alpha-derivative))
    return mp.fsum(terms)


def h_derivative(lam, order):
    """d^order/dy^order S(lam/y) at y=1, evaluated directly."""
    terms = [mp.diff(B, 1/(n*lam), order) / (n**2*(n*lam)**order)
             for n in range(1, PROFILE_N)]
    if not order:
        terms.append(profile_tail_zeta(2)/2)
    for m in range(1, PROFILE_M+1):
        alpha = 2*m-1
        if alpha >= order:
            terms.append(berncoeff(m) * profile_tail_zeta(2*m+1)
                         * mp.ff(alpha, order) * lam**(-alpha))
    return mp.fsum(terms)


def central_moment(r, order):
    # The formula is evaluated with ample working precision here; its exact
    # rational analogue is available immediately using fractions.Fraction.
    return mp.fsum((-1)**(order-j)*mp.binomial(order, j)
                   * mp.rf(r+1, j)/mp.mpf(r)**j
                   for j in range(order+1))


def D_hurwitz(r, x, ncut=32, em_order=36):
    """Normalized Herglotz jet, independently from its Hurwitz sum.

    The returned analytic truncation bound excludes floating-point roundoff.
    Euler--Maclaurin applied to zeta(r+1,n*x) yields an absolute tail
    bound by the first displayed omitted Bernoulli magnitude after summing n.
    """
    s = r+1
    # mpmath's Hurwitz evaluator can effectively target an absolute error
    # at high positive order.  The factor (n*x)^s can then magnify that
    # error enormously, so precision must include all these lost digits.
    guard = max(0, int(mp.ceil(s*mp.log10(max(mp.mpf(1), ncut*x)))))+20
    with mp.workdps(mp.mp.dps+guard):
        total = mp.fsum(((n*x)**s * mp.zeta(s, n*x) - n*x/r) / n**2
                        for n in range(1, ncut))
    total += mp.zeta(2, ncut)/2
    for m in range(1, em_order):
        total += (berncoeff(m)*mp.rf(r+1, 2*m-1)*x**(1-2*m)
                  * mp.zeta(2*m+1, ncut))
    bound = abs(berncoeff(em_order)*mp.rf(r+1, 2*em_order-1)
                * x**(1-2*em_order)*mp.zeta(2*em_order+1, ncut))
    return total, bound


def sigma_table(nmax):
    values = [mp.mpf(0) for _ in range(nmax+1)]
    for d in range(1, nmax+1):
        for n in range(d, nmax+1, d):
            values[n] += mp.mpf(1)/d
    return values


def bessel_tail_bound(lam, cutoff):
    a = 2*mp.sqrt(mp.pi/lam)
    assert a*mp.sqrt(cutoff) >= mp.mpf('1.5')
    c = 2**mp.mpf('1.5')*mp.pi**mp.mpf('.75')*lam**mp.mpf('.75')
    return (4*c*(1+1/(a*mp.sqrt(cutoff)))*a**(-mp.mpf('3.5'))
            * mp.gammainc(mp.mpf('3.5'), a*mp.sqrt(cutoff), mp.inf))


def bessel_profile(lam, cutoff):
    sigma = sigma_table(cutoff)
    terms = []
    for n in range(1, cutoff+1):
        z = 2*mp.pi*1j*n/lam
        root = mp.sqrt(z)
        terms.append(sigma[n]*mp.re(root*mp.besselk(1, 2*root)))
    return (mp.zeta(2)+lam*(mp.log(lam)-mp.euler)
            +4*lam*mp.fsum(terms))


def G_gamma(y):
    terms = [-mp.log(mp.gamma(1+1j*y/(2*mp.pi*n))
                     *mp.gamma(1-1j*y/(2*mp.pi*n)))/n
             for n in range(1, PROFILE_N)]
    for m in range(1, PROFILE_M+1):
        terms.append(berncoeff(m)*profile_tail_zeta(2*m+1)
                     *y**(2*m)/(2*m))
    return mp.re(mp.fsum(terms))


def P_dilog(y):
    terms = []
    for n in range(1, PROFILE_N):
        t = y/n
        terms.append(mp.polylog(2, mp.exp(-t))-mp.zeta(2)
                     -t*mp.log(t)+t+t*t/4)
    for m in range(1, PROFILE_M+1):
        terms.append(berncoeff(m)*profile_tail_zeta(2*m+1)
                     *y**(2*m+1)/((2*m)*(2*m+1)))
    return mp.fsum(terms)


def run():
    result = {'precision_decimal_digits': mp.mp.dps,
              'status': 'numerical checks, not a formal proof',
              'jets': [], 'certificates': [], 'bessel': [],
              'primitives': [], 'imaginary_zeros': []}
    for rawlam in ('0.25', '1', '4'):
        lam = mp.mpf(rawlam)
        s = profile(lam)
        d2, d3, d4 = (profile(lam, j) for j in (2, 3, 4))
        t1 = lam**2*d2/2
        t2 = lam**2*d2/2+2*lam**3*d3/3+lam**4*d4/8
        hd = [h_derivative(lam, j) for j in range(7)]
        t3 = hd[3]+mp.mpf(13)/12*hd[4]+mp.mpf(7)/24*hd[5]+hd[6]/48
        assert abs(t1-(hd[1]+hd[2]/2)) < mp.mpf('1e-60')
        assert abs(t2-(hd[2]+mp.mpf(5)/6*hd[3]+hd[4]/8)) < mp.mpf('1e-60')
        for r in (16, 32, 64, 128):
            val, bound = D_hurwitz(r, r*lam)
            residual = val-s-t1/r-t2/r**2
            result['jets'].append({'lambda': rawlam, 'r': r,
                                   'D': fmt(val), 'S': fmt(s),
                                   'r_cubed_residual': fmt(r**3*residual),
                                   'predicted_limit_T3': fmt(t3),
                                   'Hurwitz_tail_bound': fmt(bound)})
            if r == 32:
                approx = mp.fsum(hd[j]*central_moment(r, j)/mp.factorial(j)
                                 for j in range(6))
                cert = (2*mp.zeta(7)*mp.zeta(8)/(2*mp.pi)**7/lam**6
                        * central_moment(r, 6))
                assert abs(val-approx)+bound < cert
                result['certificates'].append({'lambda': rawlam, 'r': r,
                                               'absolute_error': fmt(abs(val-approx)),
                                               'proved_bound': fmt(cert)})
        print('jet and moment checks complete at lambda='+rawlam, flush=True)

    for rawlam in ('0.25', '0.5', '1'):
        lam = mp.mpf(rawlam)
        cutoff = int(mp.ceil(lam*750))
        val = bessel_profile(lam, cutoff)
        actual = profile(lam)
        error = abs(val-actual)
        bound = bessel_tail_bound(lam, cutoff)
        assert error <= bound+mp.mpf('1e-60')
        result['bessel'].append({'lambda': rawlam, 'cutoff': cutoff,
                                 'absolute_difference': fmt(error),
                                 'proved_tail_bound': fmt(bound),
                                 'S': fmt(actual)})
        print('Bessel check complete at lambda='+rawlam, flush=True)

    for rawy in ('0.5', '2', '5'):
        y = mp.mpf(rawy)
        err1 = abs(mp.diff(P_dilog, y)-G_gamma(y))
        err2 = abs(mp.diff(G_gamma, y)-(profile(1/y)-mp.zeta(2)/2))
        assert max(err1, err2) < mp.mpf('1e-55')
        result['primitives'].append({'y': rawy, 'P_prime_minus_G': fmt(err1),
                                     'G_prime_minus_H_centered': fmt(err2),
                                     'G': fmt(G_gamma(y)), 'P': fmt(P_dilog(y))})

    for n in (1, 2, 3):
        left = 2*mp.pi*n+mp.mpf('1e-12')
        right = 2*mp.pi*(n+1)-mp.mpf('1e-12')
        fun = lambda b: mp.im(profile(1/(1j*b)))
        assert fun(left) < 0 and fun(right) > 0
        for _ in range(110):
            mid = (left+right)/2
            if fun(mid) < 0:
                left = mid
            else:
                right = mid
        result['imaginary_zeros'].append({'N': n, 'b_approx': fmt((left+right)/2, 32),
                                           'numeric_bracket_width': fmt(right-left)})
    result['all_assertions_passed'] = True
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('herglotz_checks.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print('All checks passed; report: '+str(out), flush=True)


if __name__ == '__main__':
    run()
