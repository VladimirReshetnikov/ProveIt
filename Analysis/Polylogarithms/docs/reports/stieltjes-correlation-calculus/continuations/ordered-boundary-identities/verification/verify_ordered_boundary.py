#!/usr/bin/env python3
"""Exact finite checks and direct positive-series diagnostics.

The finite identity is tested against arbitrary rational input sequences,
not just powers.  Printed zeta examples are checked against the original
ordered sum using independently accumulated first three moments.  These
are executable diagnostics; the notes contain the general analytic proof.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
import random

import mpmath as mp
import sympy as sp


def d2(seq, k):
    return seq[k] - 2 * seq[k + 1] + seq[k + 2]


def finite_exact_tests():
    rng = random.Random(20261011)
    count = 0
    for trial in range(20):
        f = [F(rng.randrange(-11, 12), rng.randrange(1, 12))
             for _ in range(17)]
        g = [F(rng.randrange(-11, 12), rng.randrange(1, 12))
             for _ in range(17)]
        A = [F(0)] + [sum((n-m)**2 * d2(f,m) for m in range(n))
                      for n in range(1, 14)]
        for N in range(1, 13):
            direct = sum((n-m)**2 * d2(f,m) * d2(g,n)
                         for n in range(1,N+1) for m in range(n))
            band = sum(g[n] * (2*(f[0]-f[1])-f[n-1]+f[n+1])
                       for n in range(1,N+1))
            end = g[N+1]*(A[N-1]-2*A[N])+g[N+2]*A[N]
            assert direct == band + end
            explicit_A = (N*N*f[0]+(-N*N-2*N+1)*f[1]
                          +2*sum(f[2:N+1])+f[N+1])
            assert A[N] == explicit_A
            count += 1
    return count


def partial_fraction_tests():
    X, D = sp.symbols('X D', nonzero=True)
    count = 0
    for p in range(1, 7):
        for q in range(1, 7):
            terms = sum(sp.Integer(-1)**(p-k)*comb(p+q-k-1,q-1)
                        /D**(p+q-k)/X**k for k in range(1,p+1))
            terms += sum(sp.Integer(-1)**p*comb(p+q-l-1,p-1)
                         /D**(p+q-l)/(X+D)**l for l in range(1,q+1))
            assert sp.cancel(terms-1/X**p/(X+D)**q) == 0
            count += 1
    return count


def parity_tests():
    sign = lambda k: 1 if k % 2 == 0 else -1
    count = 0
    for p in range(1, 11):
        for q in range(2, 11):
            N = p + q
            for j in range(2, max(p,q)+1):
                L = comb(N-j-1,q-1) if j <= p else 0
                R = comb(N-j-1,p-1) if j <= q else 0
                direct = ((sign(q)-sign(p-j))*L
                          +(sign(q-j)-sign(p))*R)
                filtered = sign(q)*(1-sign(N-j))*(L+sign(j)*R)
                assert direct == filtered
                if (p+q+j) % 2 == 0:
                    assert direct == 0
                count += 1
    return count


def cutoff_generator_tests():
    """Compare original ordered coefficients with the root's polylog formula."""
    count = 0
    for p in range(1, 7):
        for q in range(2, 7):
            cp = (F(1)-F(1,2**p))/2
            def liqp(k):
                if k < 1:
                    return F(0)
                return sum((F(1,j**p) for j in range(1,k)),F(0))/k**q
            def lipq(k):
                return F(1,k**(p+q)) if k >= 1 else F(0)
            def B(r,s,k):
                return F(1,k**r*(k+1)**s) if k >= 1 else F(0)
            def U(k):
                return (F(1,k**q)-F(2,(k+1)**q)+F(1,(k+2)**q)
                        if k >= 1 else F(0))
            for k in range(14):
                n = k-1
                direct = F(0)
                if n >= 1:
                    for m in range(n):
                        wp=(F(1,(m+1)**p)-F(2,(m+2)**p)+F(1,(m+3)**p))/2
                        wq=(F(1,(n+1)**q)-F(2,(n+2)**q)+F(1,(n+3)**q))/2
                        direct += (n-m)**2*wp*wq
                rhs=(liqp(k+2)-2*liqp(k+1)+liqp(k))/2
                rhs+=(lipq(k)-lipq(k+1))/2
                rhs+=B(q,p,k)/4-B(p,q,k+1)/4
                rhs+=(cp*k*k-k-F(1,2))*U(k)/2
                if k == 0:
                    rhs+=F(1,2)-F(1,2**(q+2))
                assert direct == rhs, (p,q,k,direct,rhs)
                count+=1
    return count


def original_partial(p,a,q,b,N):
    """Accumulate original definition without boundary localization."""
    a, b = mp.mpf(a), mp.mpf(b)
    moments = [mp.mpf(0), mp.mpf(0), mp.mpf(0)]
    result = mp.mpf(0)
    for n in range(N+1):
        wg = ((n+b)**(-q)-2*(n+b+1)**(-q)+(n+b+2)**(-q))/2
        result += wg*(n*n*moments[0]-2*n*moments[1]+moments[2])
        wf = ((n+a)**(-p)-2*(n+a+1)**(-p)+(n+a+2)**(-p))/2
        moments[0] += wf
        moments[1] += n*wf
        moments[2] += n*n*wf
    return result


def numeric_examples():
    mp.mp.dps = 60
    cases = [
        (2,1,3,1,lambda: 3*mp.zeta(3)/8-3*mp.zeta(2)/2+mp.mpf(33)/16),
        (3,1,2,1,lambda: 31*mp.zeta(2)/16-mp.mpf(95)/32),
        (2,1,2,2,lambda: mp.zeta(4)/4+mp.zeta(2)/4-mp.mpf(9)/16),
        (2,2,2,1,lambda: 7*mp.zeta(2)/36-mp.zeta(4)/4-mp.mpf(11)/576),
    ]
    results = []
    N=4000
    for p,a,q,b,closed in cases:
        partial = original_partial(p,a,q,b,N)
        value = closed()
        aa,bb=mp.mpf(a),mp.mpf(b)
        def original_outer(n):
            # The finite inner sum is evaluated through the elementary
            # Hurwitz shift relation; no infinite boundary formula is used.
            A=(n*n*aa**(-p)+(-n*n-2*n+1)*(aa+1)**(-p)
               +2*(mp.zeta(p,aa+2)-mp.zeta(p,n+aa+1))
               +(n+aa+1)**(-p))
            return ((n+bb)**(-q)-2*(n+bb+1)**(-q)
                    +(n+bb+2)**(-q))*A/4
        accelerated=mp.nsum(original_outer,[0,mp.inf],
                            method='richardson',maxterms=2000)
        accelerated_error=abs(accelerated-value)
        assert accelerated_error < mp.mpf('1e-48')
        # Positivity and Delta^2 x^(-q) <= q(q+1)x^(-q-2)
        # yield this analytic ordinary-tail envelope.
        bound = ((mp.mpf(a)**(-p)-mp.mpf(a+1)**(-p))*q*(q+1)/4
                 *mp.zeta(q,N+b+1))
        discrepancy = value-partial
        assert 0 < discrepancy < bound
        results.append(dict(p=p,a=a,q=q,b=b,N=N,
                            value=mp.nstr(value,50),
                            partial=mp.nstr(partial,50),
                            positive_tail=mp.nstr(discrepancy,12),
                            proved_tail_envelope=mp.nstr(bound,12),
                            richardson_original_outer_sum=mp.nstr(accelerated,50),
                            richardson_absolute_error=mp.nstr(accelerated_error,12)))
    return results


def anomaly_derivative_tests():
    s, delta = sp.symbols('s delta')
    expected = [[-sp.Rational(1,2),delta/2],
                [-delta/2,(3*delta**2+1)/12]]
    for m in (0,1):
        for n in (0,1):
            j=m+n+1
            c = ((-1)**j*sp.rf(s,j)*((delta+1)**j-(delta-1)**j)
                 /(4*sp.factorial(j)))
            got=sp.diff(c,s).subs(s,-m)
            assert sp.simplify(got-expected[m][n]) == 0
    return 4


def main():
    report=dict(
        exact_finite_cutoff_checks=finite_exact_tests(),
        exact_partial_fraction_checks=partial_fraction_tests(),
        exact_parity_coefficient_checks=parity_tests(),
        exact_polylog_generator_coefficients=cutoff_generator_tests(),
        exact_anomaly_derivative_checks=anomaly_derivative_tests(),
        ordinary_series_diagnostics=numeric_examples(),
        interpretation=('Exact checks verify finite rational identities. '
                        'Numerics are direct original-series diagnostics '
                        'with analytic tail envelopes, not interval arithmetic.'))
    out=Path(__file__).with_name('ordered_boundary_checks.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
