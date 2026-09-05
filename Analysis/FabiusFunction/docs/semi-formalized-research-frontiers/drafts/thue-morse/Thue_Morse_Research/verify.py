#!/usr/bin/env python3
"""Exact and numerical checks for Thue--Morse cancellation research.

Python 3.10+; standard library only. Run `python verify.py`.
All asserted algebraic checks use integers and fractions.Fraction. Decimal
approximations in the output are illustrations, not proofs of the theorems.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb, factorial, prod, log, exp, sqrt, pi
from functools import lru_cache
import json
from pathlib import Path


def sign(n: int) -> int:
    if n < 0:
        raise ValueError('n must be nonnegative')
    return 1 if n.bit_count() % 2 == 0 else -1


def moments(nmax: int) -> list[F]:
    """mu[j] = E[Y**(2*j)], for Y=sum(2**(-k)*Uniform[-1,1])."""
    mu = [F(1)]
    for n in range(1, nmax + 1):
        mu.append(sum((comb(2*n+1, 2*k)*mu[k] for k in range(n)), F(0)) /
                  ((2*n+1)*(4**n-1)))
    return mu


def inverse_coefficients(a: list[F]) -> list[F]:
    if not a or a[0] != 1:
        raise ValueError('constant coefficient must be one')
    b = [F(1)]
    for j in range(1, len(a)):
        b.append(-sum((a[k]*b[j-k] for k in range(1, j+1)), F(0)))
    return b


@lru_cache(maxsize=None)
def spline(m: int, x: F, r: int = 0) -> F:
    """Exact positive-part formula for u_m^(r)(x).

    For r=m-1, this returns the cellwise derivative away from knots.
    The evaluation deliberately uses exact integer cancellation.
    """
    x = F(x)
    if m < 1 or not 0 <= r < m:
        raise ValueError('require m>=1 and 0<=r<m')
    a, b = x.numerator, x.denominator
    top = a*(1 << m) + b*((1 << m)-1)
    degree = m-1-r
    if top <= 0 or x >= 1-F(1,1 << m):
        return F(0)
    count = min(1 << m, (top-1)//(2*b)+1)
    signed_sum = sum(sign(n)*pow(top-2*b*n, degree) for n in range(count))
    return F((1 << (m*(m-1)//2))*signed_sum,
             factorial(degree)*pow(b*(1 << m), degree))


def qweights(p: int, q: F = F(1,4)) -> list[F]:
    if p < 0 or not 0 < q < 1:
        raise ValueError('require p>=0 and 0<q<1')
    return [prod((-q**ell/(q**j-q**ell) for ell in range(p+1) if ell != j),
                 start=F(1)) for j in range(p+1)]


@lru_cache(maxsize=None)
def dyadic_value(x: F, r: int = 0) -> F:
    """Exact u^(r)(x) using the finite local tail-averaging identity."""
    x = F(x)
    den = x.denominator
    if den & (den-1):
        raise ValueError('x must be dyadic')
    if abs(x) >= 1:
        return F(0)
    d = den.bit_length()-1
    if r > d:
        return F(0)
    m = d+2
    mu = moments((d-r)//2)
    return sum((mu[j]/factorial(2*j)*F(1,4**(m*j))*spline(m,x,r+2*j)
                for j in range((d-r)//2+1)), F(0))


def corrected(m: int, x: F, N: int, k: int = 0) -> tuple[F,F]:
    """Corrected value and rigorous global error bound."""
    if m < k+2*N+4:
        raise ValueError('regularity threshold m>=k+2N+4 required')
    mu = moments(N+1)
    value = sum((mu[j]/factorial(2*j)*F(1,4**(m*j))*spline(m,x,k+2*j)
                 for j in range(N+1)), F(0))
    r = k+2*N+2
    error = (mu[N+1]/factorial(2*N+2)*
             F(1 << (r*(r+1)//2), 4**(m*(N+1))))
    return value, error


def prefix_coefficients(m: int) -> list[int]:
    """Coefficients of product_{j<m}(1+...+z^(2^j-1)).

    Sliding windows give O(2^m) integer operations; this is not a bit-
    complexity assertion, because coefficient bit lengths grow with m.
    """
    if m < 0:
        raise ValueError('m must be nonnegative')
    a = [1]
    for j in range(m):
        width = 1 << j
        b = []
        total = 0
        for k in range(len(a)+width-1):
            if k < len(a):
                total += a[k]
            if 0 <= k-width < len(a):
                total -= a[k-width]
            b.append(total)
        a = b
    return a


def rho(m: int, k: int, coeffs: list[int] | None = None) -> F:
    a = prefix_coefficients(m) if coeffs is None else coeffs
    if not 0 <= k < len(a):
        return F(0)
    return F(a[k]*(1 << (m-1)), 1 << (m*(m-1)//2))


def lattice_point(m: int, k: int) -> F:
    return F(2*k-(1 << m)+m+1, 1 << m)


def series_multiply(a: list[F], b: list[F], N: int) -> list[F]:
    return [sum((a[k]*b[n-k] for k in range(n+1)
                 if k<len(a) and n-k<len(b)),F(0)) for n in range(N+1)]


def lattice_correction_coefficients(m: int, N: int) -> tuple[list[F],list[F]]:
    """gamma_j=[z^(2j)](z/sinh(z))^m; H_j=(-1)^j[...]/M(z)."""
    v=inverse_coefficients([F(1,factorial(2*j+1)) for j in range(N+1)])
    gamma=[F(1)]+[F(0)]*N
    power=v[:]
    exponent=m
    while exponent:
        if exponent & 1:
            gamma=series_multiply(gamma,power,N)
        power=series_multiply(power,power,N)
        exponent >>= 1
    mu=moments(N)
    b=inverse_coefficients([mu[j]/factorial(2*j) for j in range(N+1)])
    c=series_multiply(gamma,b,N)
    return gamma,[(-1)**j*c[j] for j in range(N+1)]


def checks() -> dict:
    mu = moments(8)
    a = [mu[j]/factorial(2*j) for j in range(len(mu))]
    b = inverse_coefficients(a)
    assert mu[:5] == [F(1),F(1,9),F(19,675),F(583,59535),F(132809,32531625)]
    assert b[:3] == [F(1),F(-1,18),F(31,16200)]
    assert dyadic_value(F(0)) == 1
    assert dyadic_value(F(1,2)) == F(1,2)
    assert dyadic_value(F(1,4)) == F(67,72)
    assert dyadic_value(F(1,4),2) == -8
    counts = {'prouhet':0,'derivative_identity':0,'dyadic_polynomial':0,
              'richardson':0,'prefix_convolution':0,'q_norm':0,'lattice_operator':0,'dyadic_lattice':0}
    for m in range(1,8):
        for r in range(m+1):
            value = sum(sign(n)*n**r for n in range(1 << m))
            expect = 0 if r<m else (-1)**m*factorial(m)*(1 << (m*(m-1)//2))
            assert value == expect
            counts['prouhet'] += 1
    for m in range(3,9):
        for r in range(m-1):
            for x in (F(-2,3), F(-1,4), F(0), F(1,3), F(3,4)):
                rhs = (1 << (r*(r+1)//2))*sum(
                    (sign(n)*spline(m-r,(1 << r)*x+(1 << r)-1-2*n)
                     for n in range(1 << r)),F(0))
                assert spline(m,x,r) == rhs
                counts['derivative_identity'] += 1
    for d in range(0,7):
        for num in range(-(1 << d)+1, 1 << d, 2):
            x = F(num,1 << d)
            for m in (d+2,d+3,d+4):
                for r in range(d+1):
                    target = sum((b[j]*F(1,4**(m*j))*dyadic_value(x,r+2*j)
                                 for j in range((d-r)//2+1)),F(0))
                    assert spline(m,x,r) == target
                    counts['dyadic_polynomial'] += 1
            p=d//2
            assert sum((w*spline(d+2+j,x) for j,w in enumerate(qweights(p))),F(0)) == dyadic_value(x)
            counts['richardson'] += 1
    for p in range(0,15):
        w=qweights(p)
        assert sum(w,F(0))==1
        for r in range(1,p+1):
            assert sum((w[j]*F(1,4)**(j*r) for j in range(p+1)),F(0))==0
        norm = sum(map(abs,w),F(0))
        assert norm==prod(((1+F(1,4)**j)/(1-F(1,4)**j) for j in range(1,p+1)),start=F(1))
        assert norm<2
        counts['q_norm'] += 1
    for m in range(1,9):
        c=prefix_coefficients(m)
        assert len(c)==(1 << m)-m
        assert sum(c)==(1 << (m*(m-1)//2))
        assert c==c[::-1] and min(c)>=1
        for k in range(len(c)+m):
            rhs=sum(sign(j)*comb(k-j+m-1,m-1) for j in range(min(k+1,1 << m)))
            assert rhs==(c[k] if k<len(c) else 0)
            counts['prefix_convolution'] += 1
    for m in range(2,9):
        c=prefix_coefficients(m)
        gamma,H=lattice_correction_coefficients(m,(m-1)//2)
        for k in range(-2,len(c)+2):
            x=lattice_point(m,k)
            val=sum((gamma[j]*F(1,4**(m*j))*spline(m,x,2*j)
                     for j in range(len(gamma))),F(0))
            assert val==rho(m,k,c)
            counts['lattice_operator']+=1
    for d in range(1,6):
        for m in range(d+2,d+7):
            if m%2==0:
                continue
            c=prefix_coefficients(m)
            gamma,H=lattice_correction_coefficients(m,d//2)
            for num in range(-(1 << d)+1,1 << d,2):
                x=F(num,1 << d)
                kr=((1 << m)*(x+1)-m-1)/2
                assert kr.denominator==1
                k=int(kr)
                val=sum(((-1)**j*H[j]*F(1,4**(m*j))*dyadic_value(x,2*j)
                         for j in range(d//2+1)),F(0))
                assert val==rho(m,k,c)
                counts['dyadic_lattice']+=1
    result={'counts':counts,'moments':[str(x) for x in mu[:5]],
            'a':[str(x) for x in a[:5]],'b':[str(x) for x in b[:5]],
            'dyadic_examples':[],'strong_examples':[],'lattice_examples':[],
            'theta_checks':[]}
    for d in range(1,6):
        x=F(1,1 << d)
        result['dyadic_examples'].append({'x':str(x),'u':str(dyadic_value(x)),
                                         'u2':str(dyadic_value(x,2)),
                                         'u4':str(dyadic_value(x,4)),
                                         'm':d+2,'spline':str(spline(d+2,x))})
    # Exact certified rational reference at a non-dyadic point.
    x=F(1,3)
    ref,referr=corrected(18,x,6)
    result['reference_at_one_third']={'value':str(ref),'error':str(referr),
                                    'decimal':float(ref),'error_decimal':float(referr)}
    for m in (6,8,10,12):
        row={'m':m}
        for N in (0,1,2):
            val,bound=corrected(m,x,N) if m>=2*N+4 else (None,None)
            if val is not None:
                row[f'error_N{N}']=float(abs(ref-val))
                row[f'bound_N{N}']=float(bound)
        result['strong_examples'].append(row)
    for m in (5,7,9,11,13,15):
        c=prefix_coefficients(m)
        x=F(1,4)
        k=((1 << m)*5//4-m-1)//2
        assert lattice_point(m,k)==x
        val=rho(m,k,c)
        err=val-dyadic_value(x)
        residual=err-(F(m,6)+F(1,18))*F(8,4**m)
        result['lattice_examples'].append({'m':m,'rho':str(val),
            'ratio':float(err*F(4**m,m)),'ratio_exact':str(err*F(4**m,m)),
            'residual':str(residual)})
    for alpha in (0.0,0.25,0.5):
        theta=sum(2.0**(-(k+alpha)**2) for k in range(-32,33))
        rel=[]
        for r in range(7):
            moment=sum(2.0**(-(k+alpha)**2+2*r*(k+alpha+0.5))
                       for k in range(-32,33))/theta
            rel.append(abs(moment/(2.0**(r*(r+1)))-1))
        result['theta_checks'].append({'alpha':alpha,'max_relative_error':max(rel)})
    return result


if __name__ == '__main__':
    results=checks()
    path=Path(__file__).resolve().with_name('verification_results.json')
    path.write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(results,indent=2))
    print('ALL EXACT ASSERTIONS PASSED; wrote',path)
