#!/usr/bin/env python3
"""Finite regression checks, not a proof of the arithmetic/analytic theorems."""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from random import Random
from math import isqrt


def dec(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


def hinge(t, weights):
    return sum(w * max(F(1,n)-t, F(0)) for n,w in weights.items())


def check_interpolation():
    rng=Random(18480)
    worst=Decimal(0)
    with localcontext() as ctx:
        ctx.prec=60
        for _ in range(1000):
            a=rng.randint(1,200); b=a+rng.randint(1,300)
            ta,tb=F(1,a),F(1,b)
            theta=F(rng.randrange(101),100)
            t=theta*ta+(1-theta)*tb
            weights={rng.randint(1,b+100):F(rng.randrange(100),rng.randint(1,7)) for _ in range(40)}
            # Convexity: exact rational arithmetic.
            assert hinge(t,weights)<=theta*hinge(ta,weights)+(1-theta)*hinge(tb,weights)
            j=dec(t).ln()-dec(theta)*dec(ta).ln()-dec(1-theta)*dec(tb).ln()
            bound=F(1,8)*F(b-a,a)**2
            assert j >= -Decimal('1e-55') and j <= dec(bound)+Decimal('1e-55')
            worst=max(worst,j/dec(bound))
        # Local affine-hinge equality and asymptotically sharp midpoint constant.
        for a in (100,10000,1000000):
            b=a+1
            t=(F(1,a)+F(1,b))/2
            exact=dec(t).ln()-(dec(F(1,a)).ln()+dec(F(1,b)).ln())/2
            formula=-(Decimal(1)-dec(F(b-a,b+a))**2).ln()/2
            assert abs(exact-formula)<Decimal('1e-55')
            assert exact/dec(F(1,8)*F(b-a,a)**2)>Decimal('0.98')
    print('1000 rational convexity tests and high-precision centering-gap tests passed.')
    print('Largest observed gap / universal bound:', round(worst,5))


def check_grids():
    for k in range(1,10001):
        assert (k+1)**4-k**4<=15*k**3
    prev=None
    for h in range(4,41):
        M=2**h; start=M*M//4; stop=M*M; step=2**(3*h//2)
        assert (stop-start)%step==0
        if prev is not None: assert start==prev
        assert step**2<=M**3
        # Check every point for modest h, boundary/central points for huge h.
        n=(stop-start)//step
        indices=range(1,n+1) if n<=10000 else (1,n//2,n)
        for i in indices:
            x=start+i*step
            assert (M//2)**2<x<=M**2
            # Least power of two with m^2 >= x.
            assert 2**((isqrt(x-1)).bit_length())==M
            a=x-step
            # (step/a)^2 <= 16/M, exact arithmetic.
            assert F(step,a)**2<=F(16,M)
        prev=stop
    print('Fourth powers and dyadic grid checked through h=40 (large blocks sampled).')


def check_exponents():
    for beta in (F(51,100),F(3,5),F(3,4),F(99,100)):
        prev=F(0)
        for B in (2,3,4,10,100,10000):
            A=F(B-1)*(beta-F(1,2))/(B-beta)
            assert prev<A<beta-F(1,2)
            assert A/(2)<(beta-F(1,2))/2
            prev=A
    beta=F(3,4)
    assert (beta-F(1,2))/(2-beta)==F(1,5)
    print('Three-lines and density exponent arithmetic checked exactly.')

if __name__=='__main__':
    check_interpolation(); check_grids(); check_exponents()
