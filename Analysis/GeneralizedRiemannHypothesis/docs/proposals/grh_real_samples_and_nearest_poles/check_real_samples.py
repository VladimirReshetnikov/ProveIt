#!/usr/bin/env python3
"""Exact finite regressions for the real-sample and nearest-pole argument."""
from fractions import Fraction as Q
from math import comb, factorial

# finite differences annihilate lower powers, retain the leading monomial
count = 0
for n in range(19):
    for k in range(n+1):
        assert sum((-1)**(n-j)*comb(n,j)*j**k for j in range(n+1)) == (factorial(n) if n==k else 0)
        count += 1
print('binomial moment identities:', count)

# Discrete positive real samples: write exp(hv) as a positive rational >= 1.
# The weights stand for g(v)*exp(-cv); the exact finite analogue of the integral.
weights = [Q(1,7), Q(2,3), Q(0), Q(19,5)]
bases = [Q(1), Q(5,4), Q(3,2), Q(11,7)]
for n in range(17):
    f = lambda j: sum(w*b**j for w,b in zip(weights,bases))
    d = sum((-1)**(n-j)*comb(n,j)*f(j) for j in range(n+1))
    assert d == sum(w*(b-1)**n for w,b in zip(weights,bases)) >= 0
print('positive finite sample identities: 17')

# Explicit disk centers, including high imaginary parts.
count=0
for x in [Q(3,4), Q(9,10), Q(5001,10000)]:
    beta=Q(1,2)
    for b in [(beta+x)/2,(9*x+beta)/10]:
        for y in [Q(0),Q(1),Q(100),Q(10**6)]:
            c=max(Q(3), b+1, (x*x+y*y-b*b)/(2*(x-b))+1)
            assert c>b and (c-x)**2+y*y < (c-b)**2
            count+=1
print('exact disk containment checks:',count)

# Rational complex arithmetic for Taylor coefficients of a model transform.
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def inv(a):
    d=a[0]**2+a[1]**2
    return (a[0]/d,-a[1]/d)
def power(a,n):
    z=(Q(1),Q(0))
    for _ in range(n): z=mul(z,a)
    return z
# F=K/(s-beta)+1/(s-a)-eps/2*(1/(s-b-it)+1/(s-b+it)).
# Model E is nonpositive for a>=b. For a=b the boundary obstruction is exact.
count=0
for a,b in [(Q(4,5),Q(3,4)),(Q(3,4),Q(3,4))]:
    for c in [Q(3),Q(20)]:
        for t in [Q(1,7),Q(7),Q(100)]:
            eps=Q(1,2); beta=Q(3,5)
            for n in range(41):
                z=power(inv((c-b,-t)),n+1)
                A=1/(c-beta)**(n+1)+1/(c-a)**(n+1)-eps*z[0]
                assert A>=0
                count+=1
            assert (c-a)**2 <= (c-b)**2+t*t
print('nonnegative Taylor coefficients for pole models:',count)
# A wrong-sign real pole satisfies the one-sided hypothesis: E=-exp((a-1)v).
# At a its residue is -1, not positive; same-real-part example masks complex poles.
print('wrong-sign and same-real-part obstruction: explicit residues -1, eps/2, eps/2')
print('All exact checks passed; these are finite regression tests, not a proof of the general analytic theorem.')
