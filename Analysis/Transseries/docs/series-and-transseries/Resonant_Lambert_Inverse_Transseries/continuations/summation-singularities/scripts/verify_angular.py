#!/usr/bin/env python3
"""Exact and high-precision diagnostics for the angular reconstruction.

The proofs are in the article. These finite checks are not interval
certificates. Run from any directory; outputs go to ../results.
Requires Python 3, sympy and mpmath.
"""
from pathlib import Path
import json
from fractions import Fraction
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results'
OUT.mkdir(exist_ok=True)


def convolution(x, y, length):
    z = [mp.mpf(0) for _ in range(length)]
    for i, a in enumerate(x[:length]):
        for j, b in enumerate(y[:length-i]):
            z[i+j] += a*b
    return z


def blocks_from_derivatives(derivatives):
    K = len(derivatives)
    u = sp.Symbol('u')
    B = sp.series(u/sp.sin(2*u), u, 0, K).removeO()
    beta = [mp.mpf(str(B.coeff(u, j).p))/int(B.coeff(u, j).q)
            for j in range(K)]
    S = [derivatives[j]/mp.factorial(j) for j in range(K)]
    phi = [-x for x in convolution(beta, S, K)]
    power = [mp.mpf(1)] + [mp.mpf(0)]*(K-1)
    result = []
    for k in range(1, K+1):
        power = convolution(power, phi, K)
        result.append(power[k-1]/k)
    return result


def F(a, b, z):
    """Integral continuation for a>0; exact lowering formula otherwise."""
    if a > 0:
        def kernel(t):
            w = z*mp.exp(-t)
            poly = -mp.log1p(-w) if b == 1 else mp.polylog(b, w)
            return t**(a-1)*w*poly/(1-w)
        # A finite, precision-dependent upper endpoint avoids pathological
        # huge-exponent complex logarithms in the infinite-interval rule.
        # The integrand decays as t^(a-1) exp(-2t); these remain diagnostics.
        upper = 2*mp.mp.dps+2*a+20
        return mp.quad(kernel, [0, 1, 4, 12, 40, upper])/mp.gamma(a)
    m = int(-a)
    if a != -m:
        raise ValueError('This diagnostic uses integer outer orders.')
    return sum(mp.binomial(m, j)*mp.polylog(j-m, z)*mp.polylog(b-j, z)
               for j in range(m+1))


def full_blocks(a, b, rho, K):
    derivatives = []
    for j in range(K):
        s = 2**a/rho**2*mp.im((-1j)**j*F(a-j, b, 1j*rho))
        # Exact quarter-period values avoid residual numerical sin(pi*j/2).
        s -= 2**j*(0, 1, 0, -1)[j % 4]
        derivatives.append(s)
    return blocks_from_derivatives(derivatives)


def finite_blocks(a, b, rho, M, K):
    harmonic = mp.mpf(1)
    derivatives = [mp.mpf(0) for _ in range(K)]
    for n in range(3, M+1):
        harmonic += mp.mpf(n-1)**(-b)
        weight = harmonic*rho**(n-2)*(mp.mpf(2)/n)**a
        for j in range(K):
            # d^j sin(n*pi/2 - n*u) at zero.
            quarter = (0, 1, 0, -1)[(n-j) % 4]
            derivatives[j] += weight*n**j*quarter
    return blocks_from_derivatives(derivatives)


def actual_root(a, b, rho):
    start = (1+mp.mpf(2)**(-b))*rho*(mp.mpf(2)/3)**a/2
    def equation(delta):
        return mp.im(F(a, b, rho*mp.exp(1j*(mp.pi/2-delta))))
    return mp.findroot(equation, (start*mp.mpf('.8'), start*mp.mpf('1.1')),
                       tol=mp.mpf(10)**(-mp.mp.dps+15))


def exact_checks():
    u = sp.Symbol('u')
    S = sp.symbols('S0:4')
    phi = -sp.series(u/sp.sin(2*u), u, 0, 4).removeO()*sum(
        S[j]*u**j/sp.factorial(j) for j in range(4))
    found = [sp.expand(phi**k).coeff(u, k-1)/k for k in range(1, 5)]
    expected = [-S[0]/2, S[0]*S[1]/4,
        -S[0]**3/12-S[0]**2*S[2]/16-S[0]*S[1]**2/8,
        S[0]**3*S[1]/6+S[0]**3*S[3]/96
        +3*S[0]**2*S[1]*S[2]/32+S[0]*S[1]**3/16]
    assert all(sp.expand(a-b) == 0 for a, b in zip(found, expected))
    # A rational proof certificate for the only numerical-looking constant.
    # f(x)=(x-1)/x^4 is decreasing for x>=3.
    N = 100
    partial = sum((Fraction(n-1, n**4) for n in range(3, N+1)), Fraction(0))
    integral_tail = Fraction(1, 2*N**2)-Fraction(1, 3*N**3)
    assert 243*(partial+integral_tail) < 14
    assert Fraction(14,9)-14*Fraction(2,3)**8 == Fraction(6622,6561) > 1
    assert 10*Fraction(2,3)**6 == Fraction(640,729) < 1
    assert Fraction(45696,4805) < 10
    return {'first_four_blocks': [str(sp.expand(x)) for x in found],
            'rational_derivative_constant_upper': str(243*(partial+integral_tail)),
            'status': 'passed'}


def main():
    exact = exact_checks()
    mp.mp.dps = 85
    angular = []
    for a, b in [(6,1), (8,1), (10,1)]:
        rho = mp.mpf(1)
        delta = actual_root(a, b, rho)
        coeff = full_blocks(a, b, rho, 16)
        eta = 10*rho*(mp.mpf(2)/3)**a
        for K in [1,2,4,8,12,16]:
            error = abs(delta-sum(coeff[:K]))
            bound = eta**(K+1)/(4*(K+1)*(1-eta))
            assert error < bound
            angular.append({'a': a, 'b': b, 'K': K,
                            'delta': mp.nstr(delta, 40),
                            'error': mp.nstr(error, 14),
                            'proved_bound': mp.nstr(bound, 14)})
        print('angular', a, b, 'delta =', mp.nstr(delta, 22), flush=True)
    moving = []
    for a in [20,24,28]:
        M = int(mp.floor((mp.mpf(3)/2)**(mp.mpf(a)/2)))
        K = a
        kappa = 14*M*(mp.mpf(2)/3)**a
        assert kappa < mp.mpf('.5')
        delta = actual_root(a, 1, mp.mpf(1))
        coeff = finite_blocks(a, 1, mp.mpf(1), M, K)
        error = abs(delta-sum(coeff))
        bound = 2**a*mp.mpf(M)**(2-a)/(a-2)
        bound += kappa**(K+1)/(M*(K+1)*(1-kappa))
        assert error < bound
        moving.append({'a': a, 'M': M, 'K': K,
                       'kappa': mp.nstr(kappa, 12),
                       'error': mp.nstr(error, 14),
                       'proved_bound': mp.nstr(bound, 14)})
        print('moving', a, M, K, 'error =', mp.nstr(error, 8), flush=True)
    data = {'precision_digits': mp.mp.dps, 'exact_checks': exact,
            'angular': angular, 'moving_cutoff': moving,
            'scope': 'Finite exact checks and ordinary numerical diagnostics; no interval certification.'}
    (OUT/'angular_checks.json').write_text(json.dumps(data, indent=2)+'\n')
    print('All angular diagnostics passed.', flush=True)


if __name__ == '__main__':
    main()
