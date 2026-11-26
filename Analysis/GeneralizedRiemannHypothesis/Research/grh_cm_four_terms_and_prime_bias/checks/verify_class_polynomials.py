#!/usr/bin/env python3
"""Certify ring class polynomials using CM integrality and integer intervals.

Run beside class_polynomials.json. Only the Python standard library is used.
Intervals enclose each coefficient of the analytic product; an interval
containing a unique integer and the listed integer proves their equality.
"""
import json
from math import gcd, isqrt, factorial
from pathlib import Path

BITS = 1000
S = 1 << BITS
N = 170


class I:
    """Closed real interval with endpoint denominator 2^BITS."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi

    def __add__(x,y):
        return I(x.lo + y.lo, x.hi + y.hi)

    def __neg__(x):
        return I(-x.hi, -x.lo)

    def __sub__(x,y):
        return x + (-y)

    def __mul__(x,y):
        bounds = (x.lo*y.lo, x.hi*y.lo, x.lo*y.hi, x.hi*y.hi)
        return I(min(bounds)//S, -((-max(bounds))//S))

    def __truediv__(x,y):
        assert y.lo*y.hi > 0
        return x * I(S*S//y.hi, -((-S*S)//y.lo))

    def divint(x,n):
        assert n > 0
        return I(x.lo//n,-((-x.hi)//n))

    def scale(x,n):
        if n < 0:
            return (-x).scale(-n)
        return I(x.lo*n,x.hi*n)

    def widen(x,eps):
        return I(x.lo-eps, x.hi+eps)


ZERO = I(0,0)
ONE = I(S,S)
CZERO = (ZERO,ZERO)
CONE = (ONE,ZERO)


def atan_inv(n):
    # Alternating arctangent expansion at 1/n, stopped at the first term < 1 ulp.
    value = ZERO
    sign = 1
    k = 0
    while True:
        den = (2*k+1)*n**(2*k+1)
        if den > S:
            return value.widen(1)
        value = value + ONE.divint(den).scale(sign)
        k += 1
        sign = -sign


PI = atan_inv(5).scale(16) - atan_inv(239).scale(4)


def plus(z,w):
    return (z[0]+w[0], z[1]+w[1])


def neg(z):
    return (-z[0],-z[1])


def times(z,w):
    return (z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0])


def power(z,n):
    out=CONE
    while n:
        if n%2:
            out=times(out,z)
        z=times(z,z)
        n//=2
    return out


def inverse(z):
    d=z[0]*z[0]+z[1]*z[1]
    return (z[0]/d, -z[1]/d)


def scale(z,n):
    return (z[0].scale(n), z[1].scale(n))


def widen(z,r):
    return (z[0].widen(r),z[1].widen(r))


def complex_exp(z):
    w=(z[0].divint(256), z[1].divint(256))
    assert max(abs(w[0].lo), abs(w[0].hi))+max(abs(w[1].lo),abs(w[1].hi)) < S
    out=CONE
    term=CONE
    for k in range(1,221):
        t=times(term,w)
        term=(t[0].divint(k),t[1].divint(k))
        out=plus(out,term)
    # |w| < 1, so |remainder| <= e/221! < 1 ulp.
    assert factorial(221) > 3*S
    return power(widen(out,1),256)


def forms(d):
    for a in range(1,isqrt(d//3)+1):
        for b in range(-a,a+1):
            c,rem=divmod(d+b*b,4*a)
            if rem or c<a or gcd(gcd(a,b),c)!=1:
                continue
            if (a==abs(b) or a==c) and b<0:
                continue
            yield a,b,c


sigma3 = [sum(k**3 for k in range(1,n+1) if n%k==0) for n in range(N+1)]


def singular_j(d,a,b):
    r=isqrt(d*S*S)
    root=I(r,r+1)
    q=complex_exp((-(PI*root).divint(a),(-PI).scale(b).divint(a)))
    assert (q[0]*q[0]+q[1]*q[1]).hi * 200**2 < S
    # j = E4^3 / (q prod(1-q^n)^24).
    E4=CONE
    prod=CONE
    qn=CONE
    for n in range(1,N+1):
        qn=times(qn,q)
        E4=plus(E4,scale(qn,240*sigma3[n]))
        prod=times(prod,plus(CONE,neg(qn)))
    # sigma_3(n) <= 2 n^3. Successive n^3/200^n ratios are <= 8/200.
    assert 960*(N+1)**3*S < 200**(N+1)
    E4=widen(E4,1)
    # |tail product - 1| <= exp(sum_{n>N}|q|^n)-1
    # <= 2/(199*200^N), hence < 1 ulp in either coordinate.
    assert 2*S < 199*200**N
    prod=times(prod,widen(CONE,1))
    return times(power(E4,3),inverse(times(q,power(prod,24))))


def check():
    rows=json.loads(Path(__file__).with_name("class_polynomials.json").read_text())
    for key,coeffs in rows.items():
        d=int(key)
        product=[CONE]
        for a,b,_ in forms(d):
            minus_j=neg(singular_j(d,a,b))
            product=[plus(v,times(u,minus_j)) for v,u in
                     zip([CZERO]+product,product+[CZERO])]
        assert len(product)==len(coeffs)
        for (real,imag),coeff in zip(product,coeffs):
            assert imag.lo <= 0 <= imag.hi
            assert (coeff-1)*S < real.lo <= coeff*S <= real.hi < (coeff+1)*S
    print(f"Verified {len(rows)} class polynomials ({sum(len(x)-1 for x in rows.values())} CM values).")


if __name__=="__main__":
    check()
