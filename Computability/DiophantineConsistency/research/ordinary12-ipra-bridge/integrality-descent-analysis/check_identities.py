#!/usr/bin/env python3
"""Exact polynomial identities and a bounded sanity check; no external packages."""
from itertools import product
from math import gcd

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

class P:
    names = ('q', 'd', 'v', 'n', 'a', 'b', 's', 'x', 'y', 'i')
    def __init__(self, terms=None):
        self.terms = {k: v for k, v in (terms or {}).items() if v}
    @classmethod
    def c(cls, x):
        if isinstance(x, cls): return x
        return cls({(0,) * len(cls.names): x})
    @classmethod
    def var(cls, name):
        e = [0] * len(cls.names)
        e[cls.names.index(name)] = 1
        return cls({tuple(e): 1})
    def __add__(self, other):
        other = self.c(other)
        result = self.terms.copy()
        for k, v in other.terms.items(): result[k] = result.get(k, 0) + v
        return P(result)
    __radd__ = __add__
    def __neg__(self): return P({k: -v for k, v in self.terms.items()})
    def __sub__(self, other): return self + -self.c(other)
    def __rsub__(self, other): return self.c(other) - self
    def __mul__(self, other):
        other = self.c(other)
        result = {}
        for (k, v), (l, w) in product(self.terms.items(), other.terms.items()):
            m = tuple(i + j for i, j in zip(k, l))
            result[m] = result.get(m, 0) + v*w
        return P(result)
    __rmul__ = __mul__
    def __pow__(self, n):
        r = self.c(1)
        for _ in range(n): r *= self
        return r
    def __eq__(self, other): return self.terms == self.c(other).terms

q,d,v,n,a,b,s,x,y,i = map(P.var, P.names)
w=n+v
p=1-q
h=p*w*w+q*v*v-1
bn=2*p*w
A=d*h+q*p
N=A*A-d*q*bn*bn
D=d*bn
Y=w*D-A
assert q*v*v*D*D-(q-1)*Y*Y-D*D == -(q-1)*N
assert (a*x+b*y)**3 == a*a*(a*x**3+3*b*x*x*y)+b*b*(3*a*x*y*y+b*y**3)
# Here q=1+b²s, exactly the divisor witness obtained during descent.
q0=1+b*b*s
vp=(2*q0-1)*v-2*b*s*a
ap=(2*q0-1)*a-2*q0*v*b
before=q0*v*v*b*b-(q0-1)*a*a-b*b
after=q0*vp*vp*b*b-(q0-1)*ap*ap-b*b
assert after == before
assert ap-a == b*(2*b*s*a-2*q0*v)
assert (d*bn*i)**2-d*q*bn**2 == d*bn**2*(d*i*i-q)

count=0
max_v=0
for qv in range(2, 10):
    for bv in range(1, 10):
        for vv in range(1, 26):
            for av in range(1, 201):
                if gcd(av, bv) != 1 or qv*vv*vv*bv*bv != (qv-1)*av*av+bv*bv:
                    continue
                count += 1
                max_v=max(max_v,vv)
                assert (qv-1) % (bv*bv) == 0
                if vv == 1:
                    assert av == bv == 1
                    continue
                assert av > vv*bv and qv*vv*bv > (qv-1)*av
                vnext=(2*qv-1)*vv-2*((qv-1)//bv)*av
                anext=(2*qv-1)*av-2*qv*vv*bv
                assert 0 < abs(vnext) < vv
                assert gcd(abs(anext), bv) == 1
                assert qv*vnext*vnext*bv*bv == (qv-1)*anext*anext+bv*bv
                assert bv == 1
# Q=1 permits any rational y when v=1, including 1/2.
assert 1*1*1*2*2 == (1-1)*1*1+2*2
print(f'PASS: five exact polynomial identities; {count} bounded reduced norm states, largest v={max_v}; Q=1 counterexample checked')
