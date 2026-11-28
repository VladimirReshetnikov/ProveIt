#!/usr/bin/env python3
"""Exact checks for the Archimedean chart bound in two CM fields.

Uses only Python's standard library. Quadratic real coordinates in the quartic
example are pairs (a,b) representing a+b*sqrt(2).  Square roots are never
approximated. The finite samples are regression tests for the identities.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd

def sub(x, y):
    return (x[0]-y[0], x[1]-y[1])

def add(x, y):
    return (x[0]+y[0], x[1]+y[1])

def cubic_weight_check(heights, f):
    for B in (1, 2, 4, 16, 64, 256):
        assert sum(h <= B for h in heights) <= 18**f * B**2
    assert sum((F(1)/h**3 for h in heights), F(0)) <= 3*18**f

def quadratic():
    # Integers of Q(sqrt(-5)) are Z[t], t^2=-5; the class group is nontrivial.
    def norm(z):
        return z[0]**2 + 5*z[1]**2
    def inv(z):
        n = norm(z)
        return (z[0]/n, -z[1]/n)
    xs = {}
    for m in range(1, 5):
        for a, b in product(range(-3, 4), range(-2, 3)):
            z = (F(a,m), F(b,m))
            # D_z is the kernel of O -> O/(m), v -> v*(a+b*t).
            image = {((u*a-5*v*b)%m, (u*b+v*a)%m)
                     for u, v in product(range(m), repeat=2)}
            D = len(image)
            N = norm(z)
            chart = N > 1
            height = D*max(1,N)
            row = (chart, inv(z) if chart else z, D, height)
            assert xs.setdefault(z,row) == row
    # The denominator ideal of (1+t)/2 has norm 2, hence is nonprincipal:
    # the norm form a^2+5b^2 never equals 2.
    assert xs[F(1,2), F(1,2)][2] == 2
    equal_chart = 0
    for (x, (c, u, D, H)), (y,(e, v, E, G)) in combinations(xs.items(),2):
        ideal_norm = D*E*norm(sub(x,y))
        assert ideal_norm.denominator == 1 and ideal_norm >= 1
        if c == e:
            assert norm(sub(u,v))*H*G == ideal_norm
            equal_chart += 1
    cubic_weight_check([t[-1] for t in xs.values()], 1)
    print(f'Q(sqrt(-5)): {len(xs)} points, {equal_chart} equal-chart pairs, nonprincipal denominator verified')

ONE = (F(1), F(0))

def rmul(x,y):
    return (x[0]*y[0]+2*x[1]*y[1], x[0]*y[1]+x[1]*y[0])

def rconj(x):
    return (x[0], -x[1])

def rdiv(x,y):
    n = rmul(y,rconj(y))[0]
    z = rmul(x,rconj(y))
    return (z[0]/n,z[1]/n)

def sign(x):
    a,b=x
    if a >= 0 and b >= 0: return int((a,b) != (0,0))
    if a <= 0 and b <= 0: return -int((a,b) != (0,0))
    cmp = (a*a > 2*b*b) - (a*a < 2*b*b)
    return cmp if a > 0 else -cmp

def csquare(z):
    return add(rmul(z[0],z[0]),rmul(z[1],z[1]))

def cinverse(z):
    den=csquare(z)
    return (rdiv(z[0],den),rdiv((-z[1][0],-z[1][1]),den))

def csub(z,w):
    return (sub(z[0],w[0]),sub(z[1],w[1]))

def rle(x,y):
    return sign(sub(x,y)) <= 0

def quartic():
    # E=Q(sqrt(2),i). Use integral numerators and rational denominators m
    # coprime to the norm of that numerator. Then D_(z/m)=m O_E.
    pts = {}
    for m in (1,3):
        for a,b,c,d in product(range(-1,2), repeat=4):
            z = ((F(a,m),F(b,m)),(F(c,m),F(d,m)))
            z2 = (rconj(z[0]),rconj(z[1]))
            n1,n2=csquare(z),csquare(z2)
            abs_norm=rmul(n1,n2)
            assert abs_norm[1]==0
            if gcd(int(abs_norm[0]*m**4),m)!=1: continue
            chart=(not rle(n1,ONE),not rle(n2,ONE))
            uf=tuple(cinverse(w) if cbit else w for cbit,w in zip(chart,(z,z2)))
            A=rmul(n1 if chart[0] else ONE,n2 if chart[1] else ONE)
            H=rmul(A,(F(m**4),F(0)))
            assert all(rle(csquare(u),ONE) for u in uf)
            pts[z]=(chart,uf,H,m**4)
    assert {t[0] for t in pts.values()}==set(product((False,True), repeat=2))
    pairs = 0
    for (x,(c,u,H,D)),(y,(e,v,G,E)) in combinations(pts.items(),2):
        n=csquare(csub(x,y))
        J=rmul(n,rconj(n))[0]*D*E
        assert J.denominator==1 and J>=1
        if c!=e: continue
        ds=[csquare(csub(ui,vi)) for ui,vi in zip(u,v)]
        assert rmul(rmul(ds[0],ds[1]),rmul(H,G))==(J,F(0))
        B=G if rle(H,G) else H
        maximum=ds[1] if rle(ds[0],ds[1]) else ds[0]
        # f=2: separation squared is at least B^{-1}.
        assert rle(ONE,rmul(maximum,B))
        pairs+=1
    for B in (1,2,4,16,64,256):
        assert sum(rle(t[2],(F(B),F(0))) for t in pts.values()) <= 18**2*B**2
    print(f'Q(sqrt(2),i): {len(pts)} points, {pairs} equal-chart pairs, all four chart patterns verified')

if __name__ == '__main__':
    quadratic()
    quartic()
