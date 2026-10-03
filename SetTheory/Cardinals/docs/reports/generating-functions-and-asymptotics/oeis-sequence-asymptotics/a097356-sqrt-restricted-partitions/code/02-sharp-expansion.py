#!/usr/bin/env python3
"""All-orders saddle coefficients for square-shell restricted partitions.

Only numerical constants are evaluated with mpmath. Exact partition counts are
computed separately in verify.py; rigorous sign enclosures are in certify.py.
"""
from __future__ import annotations
import math
from collections import defaultdict
import mpmath as mp


def constants(dps: int = 70) -> dict:
    mp.mp.dps = dps
    def F(z):
        return (mp.pi**2 / 6 - mp.polylog(2, mp.exp(-z))) / z
    v = mp.findroot(lambda z: -mp.diff(F, z) - 1, (mp.mpf('.7'), mp.mpf('.9')))
    B = mp.diff(F, v, 2)
    h = lambda z: mp.log(z / (-mp.expm1(-z))) / 2
    u = lambda r, z: (-mp.bernoulli(2*r) * z**(2*r-1) /
                       mp.factorial(2*r) *
                       (mp.polylog(2-2*r, mp.exp(-z)) +
                        (mp.mpf('0.5') if r == 1 else 0)))
    s = -mp.expm1(-v)
    beta = -mp.log(s)
    g = 2*v + beta
    C = mp.exp(h(v)) / (2*mp.pi*mp.sqrt(B))
    h1, h2 = mp.diff(h, v), mp.diff(h, v, 2)
    f3, f4 = mp.diff(F, v, 3), mp.diff(F, v, 4)
    eta = -h1/B + f3/(2*B**2)
    d0 = (u(1,v) - (h2+h1*h1)/(2*B) + h1*f3/(2*B**2)
          + f4/(8*B**2) - 5*f3*f3/(24*B**3))
    linear = 2+2*eta
    quadratic = v-2/B
    tail = d0+linear+quadratic+beta/2
    return dict(F=F,h=h,u=u,v=v,B=B,s=s,beta=beta,g=g,C=C,d=mp.exp(g),
                lower=C*s,d0=d0,eta=eta,linear=linear,quadratic=quadratic,
                tail=tail,rho=2*v/g,jump=1/s)


def mul(a: dict, b: dict) -> dict:
    c = defaultdict(mp.mpf)
    for (i,j), x in a.items():
        for (k,l), y in b.items():
            c[i+k,j+l] += x*y
    return dict(c)


def saddle_polynomials(order: int = 4, dps: int = 70) -> tuple[dict,list[list]]:
    """Return constants and coefficient lists P_j(t), constant term first.

    The polynomial dictionary uses (degree in w, degree in t). Gaussian
    contraction sends w^(2r) to (-1)^r (2r-1)!! / B^r.
    """
    if order < 0:
        raise ValueError('order must be nonnegative')
    c = constants(dps)
    F,h,u,v,B = (c[k] for k in ('F','h','u','v','B'))
    gammas = [{}]
    for j in range(1,2*order+1):
        p = defaultdict(mp.mpf)
        p[j,0] += mp.diff(h,v,j)/mp.factorial(j)
        p[j+2,0] += mp.diff(F,v,j+2)/mp.factorial(j+2)
        if j == 1:
            p[1,1] += 1
        for r in range(1,(j+2)//4+1):
            ell=j-(4*r-2)
            if ell >= 0:
                p[ell,0] += mp.diff(lambda z: u(r,z),v,ell)/mp.factorial(ell)
        gammas.append(dict(p))
    E=[{(0,0):mp.mpf(1)}]
    for j in range(1,2*order+1):
        p=defaultdict(mp.mpf)
        for ell in range(1,j+1):
            for key,val in mul(gammas[ell],E[j-ell]).items():
                p[key] += mp.mpf(ell)/j*val
        E.append(dict(p))
    result=[]
    for j in range(order+1):
        coeff=[mp.mpf(0)]*(2*j+1)
        for (power,degree),val in E[2*j].items():
            assert power%2 == 0
            r=power//2
            moment=(-1)**r*mp.factorial(2*r)/(2**r*mp.factorial(r)*B**r)
            coeff[degree] += val*moment
        result.append(coeff)
    return c,result


def poly(coeff: list, t):
    return mp.polyval(list(reversed(coeff)),t)


def approximation(n: int, m: int, c: dict, polys: list[list], order: int):
    if n < 0 or m <= 0 or order < 0 or order >= len(polys):
        raise ValueError('invalid n, m, or expansion order')
    t=mp.mpf(n-m*m)/m
    correction=sum(poly(polys[j],t)/mp.mpf(m)**j for j in range(order+1))
    return c['C']*mp.exp(c['g']*m+c['v']*t)/mp.mpf(m)**2*correction


def inverse_prediction(y, c: dict):
    """Return the leading phase-aware prediction for the integer threshold."""
    y=mp.mpf(y)
    if not mp.isfinite(y) or y <= 0:
        raise ValueError('y must be a positive finite real threshold')
    x0=-2/c['g']*mp.lambertw(-c['g']/2*mp.sqrt(c['C']/y),-1)
    if abs(mp.im(x0)) > mp.mpf('1e-30'):
        raise ValueError('y is too small for the real large-argument branch')
    x0=mp.re(x0)
    k=int(mp.floor(x0)); theta=x0-k
    return (k+min(theta/c['rho'],mp.mpf(1)))**2


if __name__ == '__main__':
    c,p=saddle_polynomials()
    for key,val in c.items():
        if not callable(val):
            print(key,mp.nstr(val,50))
    for j,co in enumerate(p):
        print('P'+str(j),[mp.nstr(x,35) for x in co])
