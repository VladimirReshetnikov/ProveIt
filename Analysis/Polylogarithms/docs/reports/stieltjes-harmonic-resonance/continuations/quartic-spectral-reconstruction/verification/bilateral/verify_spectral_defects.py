#!/usr/bin/env python3
"""Independent exact algebra and high-precision diagnostics for spectral defects.

No numerical result here substitutes for the accompanying analytic proof.
Run with Python 3 and mpmath. Output is JSON; no network access is needed.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 75


def m(x):
    if isinstance(x, F):
        return mp.mpf(x.numerator) / x.denominator
    return mp.mpf(x)


def one_factor_coeffs(B, Q, K):
    """Exact coefficients [z^q s^j](1+B*z)^(-s), via Pochhammer."""
    out = [[F(0) for _ in range(K + 1)] for _ in range(Q + 1)]
    out[0][0] = F(1)
    for q in range(1, Q + 1):
        for j in range(K + 1):
            out[q][j] = -B / q * ((q - 1) * out[q-1][j]
                                      + (out[q-1][j-1] if j else 0))
    return out


def spectrum_coeffs(Bs, Q, K):
    """Product of quadratic factors, retaining spectral jets exactly."""
    out = [[F(0) for _ in range(K + 1)] for _ in range(Q + 1)]
    out[0][0] = F(1)
    for B in Bs:
        fac = one_factor_coeffs(B, Q, K)
        new = [[F(0) for _ in range(K + 1)] for _ in range(Q + 1)]
        for q in range(Q + 1):
            for j in range(K + 1):
                new[q][j] = sum(out[t][h] * fac[q-t][j-h]
                                for t in range(q+1) for h in range(j+1))
        out = new
    return out


def multiply_z(f, g, Q):
    return [sum(f[j] * g[q-j] for j in range(q+1)) for q in range(Q+1)]


def power_z(f, power, Q):
    out = [F(1)] + [F(0)] * Q
    for _ in range(power):
        out = multiply_z(out, f, Q)
    return out


def direct_log_coeffs(Bs, k, Q):
    """Independent [z^q log(v)^h] expansion of the raw k-th defect."""
    r = len(Bs)
    us = [[F(0)] + [(-1)**(q+1) * B**q / q for q in range(1, Q+1)]
          for B in Bs]
    total = [sum(u[q] for u in us) for q in range(Q+1)]
    out = [[F(0) for _ in range(k+1)] for _ in range(Q+1)]
    for h in range(k+1):
        individual = [power_z(u, k-h, Q) for u in us]
        combined = power_z(total, k-h, Q)
        for q in range(Q+1):
            out[q][h] = ((-1)**k * comb(k, h)
                         * (r**(k-1) * sum(v[q] for v in individual)
                            - r**h * combined[q]))
    return out


def exact_algebra_checks():
    checks = 0
    for Bs in ([F(1), F(4)], [F(1,4), F(1), F(9,4)],
               [F(1,3), F(2,3), F(3,2), F(5,2)]):
        r, Q, K = len(Bs), 8, 6
        prod = spectrum_coeffs(Bs, Q, K)
        singles = [one_factor_coeffs(B, Q, K) for B in Bs]
        aq = [[sum(c[q][j] for c in singles) * F(r**j, r) - prod[q][j]
               for j in range(K+1)] for q in range(Q+1)]
        for q in range(Q+1):
            assert aq[q][0] == aq[q][1] == 0
            checks += 2
        assert all(aq[q][j] == 0 for q in (0,1) for j in range(K+1))
        checks += 2*(K+1)
        for k in range(2,K+1):
            raw = direct_log_coeffs(Bs,k,Q)
            for q in range(Q+1):
                for h in range(k+1):
                    expected = F(factorial(k), factorial(h)) * aq[q][k-h] * (-r)**h
                    assert raw[q][h] == expected, (Bs,k,q,h)
                    checks += 1
        raw2 = direct_log_coeffs(Bs,2,Q)
        for q in range(Q+1):
            pair = F(0)
            for i in range(r):
                for j in range(i+1,r):
                    ds = [F(0)] + [(-1)**(n+1)*(Bs[i]**n-Bs[j]**n)/n
                                   for n in range(1,Q+1)]
                    pair += multiply_z(ds,ds,Q)[q]
            assert raw2[q][0] == pair
            checks += 1
    return checks


@lru_cache(maxsize=None)
def hurwitz_pair_derivative(order, a, N, derivative):
    aa = m(a)
    return (mp.zeta(order, N+aa, derivative=derivative)
            + mp.zeta(order, N+1-aa, derivative=derivative))


def spectral_jet(P, Bs, a, k, N=8, Q=52):
    """Independent head/tail continuation of each spectral zeta."""
    aa, r = m(a), len(Bs)
    head = mp.mpf(0)
    for n in range(N):
        for shift in (aa, 1-aa):
            v = (n+shift)**2
            pp = sum(m(p)*v**d for d,p in enumerate(P))
            ll = sum(mp.log(v+m(B)) for B in Bs)
            head += pp * (-ll)**k
    cc = spectrum_coeffs(Bs,Q,k)
    tail = mp.mpf(0)
    for d,p in enumerate(P):
        if not p:
            continue
        for q in range(Q+1):
            for j in range(k+1):
                if cc[q][j]:
                    tail += (m(p*cc[q][j]) * factorial(j) * comb(k,j)
                             * (2*r)**(k-j)
                             * hurwitz_pair_derivative(2*q-2*d,a,N,k-j))
    return head+tail


def direct_subtracted_jet(P, Bs, a, k, N=8, Q=52):
    """Ordinary subtracted log sum; counterterm returned separately.

    The logarithmic power series is constructed directly, independently
    of the Pochhammer spectral-continuation implementation above.
    """
    raw = direct_log_coeffs(Bs,k,Q)
    r, aa = len(Bs), m(a)
    head, tail, counter = mp.mpf(0), mp.mpf(0), mp.mpf(0)
    for n in range(N):
        for shift in (aa,1-aa):
            v=(n+shift)**2
            ll=[mp.log(v+m(B)) for B in Bs]
            pp=sum(m(p)*v**d for d,p in enumerate(P))
            f=(-1)**k*pp*(r**(k-1)*sum(t**k for t in ll)-sum(ll)**k)
            subtraction=sum(m(p*raw[q][h])*v**(d-q)*mp.log(v)**h
                            for d,p in enumerate(P) for q in range(d+1)
                            for h in range(k+1) if p and raw[q][h])
            head+=f-subtraction
    for d,p in enumerate(P):
        if not p:
            continue
        for q in range(Q+1):
            for h in range(k+1):
                if not raw[q][h]:
                    continue
                coef=m(p*raw[q][h])*(-2)**h
                if q>d:
                    tail += coef*hurwitz_pair_derivative(2*q-2*d,a,N,h)
                elif h:
                    counter += coef*hurwitz_pair_derivative(2*q-2*d,a,0,h)
                # h=0 terms are exactly zero by Bernoulli reflection.
    return head+tail, counter


def resolvent(a,t):
    b=mp.sqrt(t)
    return mp.pi/b*mp.sinh(2*mp.pi*b)/(mp.cosh(2*mp.pi*b)-mp.cos(2*mp.pi*m(a)))


def quadrature(P,a,B,C):
    B,C=m(B),m(C)
    if B==C:
        return mp.mpf(0)
    if B<C:
        B,C=C,B
    f=lambda t: sum(m(p)*(-t)**d for d,p in enumerate(P))*resolvent(a,t)
    span=B-C
    return 2*span*mp.quad(lambda x:(f(C+span*x)-f(B-span*x))
                          *mp.log((1-x)/x),[0,mp.mpf('0.25'),mp.mpf('0.5')])


def main():
    out={'precision_digits':mp.mp.dps,'exact_fraction_checks':exact_algebra_checks(),
         'note':'Numerical diagnostics are not interval certificates or proofs.',
         'numeric_checks':[]}
    cases=[('unweighted_two',[F(1)],[F(1),F(4)],F(1,2),2),
           ('linear_three',[F(1),F(2)],[F(1,4),F(1),F(9,4)],F(2,5),2),
           ('quartic_weight_two',[F(0),F(0),F(1)],[F(1),F(4)],F(1,2),2),
           ('third_jet_counterterm',[F(0),F(0),F(1)],[F(1),F(4)],F(1,2),3),
           ('fourth_jet_three',[F(1),F(-2),F(3)],[F(1,4),F(1),F(9,4)],F(2,5),4)]
    for name,P,Bs,a,k in cases:
        r=len(Bs)
        spectral=(r**(k-1)*sum(spectral_jet(P,[B],a,k) for B in Bs)
                  -spectral_jet(P,Bs,a,k))
        ordinary,counter=direct_subtracted_jet(P,Bs,a,k)
        row={'name':name,'k':k,'spectral_defect':mp.nstr(spectral,55),
             'ordinary_remainder':mp.nstr(ordinary,55),
             'finite_counterterm':mp.nstr(counter,55),
             'spectral_minus_reconstructed':mp.nstr(spectral-ordinary-counter,8)}
        assert abs(spectral-ordinary-counter)<mp.mpf('1e-48'),row
        if k==2:
            integ=sum(quadrature(P,a,Bs[i],Bs[j])
                      for i in range(r) for j in range(i+1,r))
            row['resolvent_quadrature']=mp.nstr(integ,55)
            row['quadrature_minus_series']=mp.nstr(integ-ordinary,8)
            assert abs(integ-ordinary)<mp.mpf('1e-48'),row
        if name=='third_jet_counterterm':
            expected=-12*(m(Bs[0])-m(Bs[1]))**2*mp.log(2*mp.sin(mp.pi*m(a)))
            row['closed_counterterm']=mp.nstr(expected,55)
            assert abs(expected-counter)<mp.mpf('1e-68')
        out['numeric_checks'].append(row)
    a,C,h=F(1,2),mp.mpf(1),mp.mpf('0.001')
    f=lambda t:resolvent(a,t)
    confluent=-2*sum(mp.harmonic(k-1)/mp.factorial(k)*mp.diff(f,C,k-1)*h**k
                     for k in range(2,16))
    integral=quadrature([F(1)],a,C+h,C)
    coefficient=mp.pi/2*mp.tanh(mp.pi)-mp.pi**2/2/mp.cosh(mp.pi)**2
    out['confluence']={'a':'1/2','C':'1','h':'0.001','retained_through':15,
        'series':mp.nstr(confluent,55),'quadrature':mp.nstr(integral,55),
        'difference':mp.nstr(confluent-integral,8),
        'quadratic_coefficient':mp.nstr(coefficient,55)}
    assert abs(confluent-integral)<mp.mpf('1e-44')
    path=Path(__file__).with_name('verification.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
