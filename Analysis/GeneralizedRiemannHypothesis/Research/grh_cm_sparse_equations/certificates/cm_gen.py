#!/usr/bin/env python3
"""Certify 79 CM class polynomials using only Python integer arithmetic.
Print JSON in ascending coefficient order.  Python >= 3.8, no dependencies.
"""
from dataclasses import dataclass
from math import factorial, gcd, isqrt
import json
import os
import sys

DEGREE_FOUR = (39,55,56,63,68,80,128,136,144,155,156,171,184,196,203,208,
               219,220,252,256,259,275,291,292,323,328,355,363,387,388,
               400,475,507,568,592,603,667,723,763,772,955,1003,1027,1227,
               1243,1387,1411,1467,1507,1555)
DEGREE_FIVE = (47,79,103,127,131,179,188,227,316,347,412,443,508,523,571,
               619,683,691,739,787,947,1051,1123,1723,1747,1867,2203,2347,2683)
# Additional precision is used for the largest polynomials in the extended census.
BITS = int(os.environ.get('CM_INTERVAL_BITS', '1240'))
assert BITS >= 1240
S = 1 << BITS
K = 160 + (BITS-1240)//7
T = 190 + (BITS-1240)//6

def ceildiv(a, b):
    return -((-a) // b)

@dataclass(frozen=True)
class I:
    """Closed interval with integer numerators and the common denominator S."""
    lo: int
    hi: int

    def __add__(self, b):
        return I(self.lo + b.lo, self.hi + b.hi)

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, b):
        return self + (-b)

    def __mul__(self, b):
        vals = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return I(min(vals)//S, ceildiv(max(vals), S))

    def divint(self, b):
        assert b > 0
        return I(self.lo//b, ceildiv(self.hi, b))

    def scale(self, b):
        v, w = self.lo*b, self.hi*b
        return I(min(v,w), max(v,w))

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return I(S*S//self.hi, ceildiv(S*S, self.lo))

def integer(n):
    return I(n*S, n*S)

def boxerr(n, d):
    r = ceildiv(n*S,d)
    return I(-r,r)

Z = integer(0)
O = integer(1)
def re(x):
    return (integer(x), Z)
def cadd(a,b):
    return (a[0]+b[0], a[1]+b[1])
def cneg(a):
    return (-a[0], -a[1])
def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def cscale(a,n):
    return (a[0].scale(n),a[1].scale(n))
def cdivint(a,n):
    return (a[0].divint(n),a[1].divint(n))
def cinverse(a):
    norm = a[0]*a[0] + a[1]*a[1]
    t = norm.reciprocal()
    return (a[0]*t,-a[1]*t)

def arctan_inv(n):
    """Alternating rational bounds for arctan(1/n)."""
    ans, power, sign, k = Z, n, 1, 0
    while True:
        den = (2*k+1)*power
        if den > S:
            return ans + boxerr(1,den)
        term = O.divint(den)
        ans += term.scale(sign)
        power *= n*n
        sign, k = -sign, k+1

PI = arctan_inv(5).scale(16) - arctan_inv(239).scale(4)
def q_value(D,a,b):
    u = isqrt(D*S*S)
    sqrtD = I(u,u+1)
    # Scale high discriminants further so the exponential Taylor remainder
    # is evaluated on the same unit disk used for the small census.
    squarings = max(8, (4*(isqrt(D)+1+abs(b))//a).bit_length())
    denominator = a*(1 << squarings)
    y = (-(PI*sqrtD).divint(denominator), -(PI.scale(b)).divint(denominator))
    absolute_upper = max(abs(y[0].lo),abs(y[0].hi)) + max(abs(y[1].lo),abs(y[1].hi))
    assert absolute_upper <= S
    # For |y|<=1 the exponential remainder is <= 3/(T+1)!.
    w = re(1)
    for n in range(T,0,-1):
        w = cadd(re(1),cdivint(cmul(y,w),n))
    err = boxerr(3,factorial(T+1))
    w = cadd(w,(err,err))
    for _ in range(squarings):
        w = cmul(w,w)
    # The omitted-series bound below uses |q| <= 1/200.
    def mag(x):
        return max(abs(x.lo),abs(x.hi))
    assert 200**2*(mag(w[0])**2+mag(w[1])**2) <= S*S
    return w

def sigma_list(k):
    sigma = [0]*(K+1)
    for d in range(1,K+1):
        d_power = d**k
        for n in range(d,K+1,d):
            sigma[n] += d_power
    return sigma

S3, S5 = sigma_list(3), sigma_list(5)
def eisenstein(q, k, sigma, multiplier):
    s = re(0)
    for n in range(K,0,-1):
        s = cadd(re(sigma[n]),cmul(q,s))
    s = cadd(re(1),cscale(cmul(q,s),multiplier))
    # sigma_k(n) <= 2*n**k. For n>K the successive ratios
    # of n**k/200**n are <1/2. Enclose absolute complex error.
    err = boxerr(4*abs(multiplier)*(K+1)**k,200**(K+1))
    return cadd(s,(err,err))

def singular_modulus(D,a,b):
    q = q_value(D,a,b)
    e4 = eisenstein(q,3,S3,240)
    e6 = eisenstein(q,5,S5,-504)
    cube = cmul(e4,cmul(e4,e4))
    denom = cadd(cube,cneg(cmul(e6,e6)))
    return cscale(cmul(cube,cinverse(denom)),1728)

def reduced_forms(D):
    for a in range(1,isqrt(D//3)+1):
        for b in range(-a,a+1):
            c,r = divmod(b*b+D,4*a)
            if r or c<a or ((abs(b)==a or a==c) and b<0):
                continue
            if gcd(gcd(a,b),c)==1:
                yield a,b,c

def class_polynomial(D):
    poly = [re(1)]
    for a,b,c in reduced_forms(D):
        neg_root = cneg(singular_modulus(D,a,b))
        poly = [cadd(x,y) for x,y in zip([cmul(c,neg_root) for c in poly]+[re(0)],
                                         [re(0)]+poly)]
    coeff = []
    for real,imag in poly:
        # CM theory supplies integrality. Each box must contain a
        # unique real integer and its imaginary part must contain zero.
        n = ceildiv(real.lo,S)
        assert n == real.hi//S and imag.lo <= 0 <= imag.hi
        coeff.append(n)
    return coeff

def main():
    results = {}
    for D in sorted(DEGREE_FOUR+DEGREE_FIVE):
        polynomial = class_polynomial(D)
        assert len(polynomial) == (5 if D in DEGREE_FOUR else 6)
        assert polynomial[-1] == 1 and polynomial[0] != 0
        results[str(D)] = polynomial
    json.dump(results,sys.stdout,indent=2)
    print()

if __name__ == '__main__':
    main()
