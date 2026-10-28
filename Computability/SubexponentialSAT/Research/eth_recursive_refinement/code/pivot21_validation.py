#!/usr/bin/env python3
"""Independent exact checks for the residue-aware 21-pivot Cauchy expansion.

This is an algebraic research check, not an end-to-end SAT solver.
Only Python's standard library is required.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import factorial, comb
import json

def require(condition, message="exact validation failed"):
    """Checks remain active under python -O."""
    if not condition:
        raise RuntimeError(message)


PATTERN = "ABABCABABCABAACABAACA"
# 21 positions, 11 A, 6 B, 4 C; C positions (zero based) 4,9,14,19.
require(len(PATTERN) == 21, "pattern length")
require(tuple(PATTERN.count(c) for c in "ABC") == (11, 6, 4), "pattern counts")

def v2(q):
    q = F(q)
    if not q:
        return 10**9
    def vi(n):
        n = abs(n)
        return (n & -n).bit_length() - 1
    return vi(q.numerator) - vi(q.denominator)

def vf(n):
    return n - n.bit_count()

@dataclass(frozen=True)
class E:
    """Exact Q[U]/(U^2+U+1), unramified at 2."""
    a: F = F(0)
    b: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))
    def __add__(self, other):
        o = cv(other)
        return E(self.a+o.a, self.b+o.b)
    __radd__ = __add__
    def __neg__(self):
        return E(-self.a, -self.b)
    def __sub__(self, other):
        return self + -cv(other)
    def __rsub__(self, other):
        return cv(other) + -self
    def __mul__(self, other):
        o = cv(other)
        return E(self.a*o.a-self.b*o.b,
                 self.a*o.b+self.b*o.a-self.b*o.b)
    __rmul__ = __mul__
    def inv(self):
        n = self.a*self.a-self.a*self.b+self.b*self.b
        if not n:
            raise ZeroDivisionError
        return E((self.a-self.b)/n, -self.b/n)
    def __truediv__(self, other):
        return self * cv(other).inv()
    def __rtruediv__(self, other):
        return cv(other) * self.inv()
    def valuation(self):
        return min(v2(self.a), v2(self.b))
    def residue8(self):
        if self.valuation() < 0:
            raise ValueError("nonintegral")
        def rr(q):
            return q.numerator*pow(q.denominator, -1, 8)%8
        return rr(self.a), rr(self.b)

def cv(x):
    return x if isinstance(x, E) else E(x)

def pivots(n, c):
    counts = {a:0 for a in "ABC"}
    out = []
    for h in range(n):
        tag = PATTERN[h%21]
        k = counts[tag]
        out.append(1+2*k if tag == "A" else 4*k if tag == "B" else c+8*k)
        counts[tag] += 1
    return out

def counts(b):
    q, r = divmod(b, 21)
    return tuple(q*PATTERN.count(a)+PATTERN[:r].count(a) for a in "ABC")

def eta(b):
    A,B,C = counts(b)
    return min(A+vf(A), 2*B+vf(B)+C, 3*C+vf(C)+B)

def weight(b):
    return 1+b+vf(b)+eta(b)

def features(z, j, J, c):
    """Return (target, source) pairs for c_x=1, exactly in Q(U)."""
    rho = [2*v for v in pivots(J,c)]
    row = E(1)
    colden = 1
    out = []
    for b in range(J):
        colden *= 1-rho[b]*j
        r = factorial(b)*row/(1-b*z)
        ell = F((1-b*rho[b])*comb(j,b), colden) if b<=j else F(0)
        out.append((r,ell))
        row *= (z-rho[b])/(1-b*z)
    return out

def check():
    stats = {"prefix_checks":0,"integer_domain_checks":0,
             "actual_domain_checks":0,"extension_domain_checks":0,
             "exact_separation_checks":0,"target_weight_checks":0}
    for b in range(10000):
        A,B,C = counts(b)
        require(A+B+C == b, "prefix sum")
        require(C <= b//4, "C-prefix precision allowance")
        if b:
            require(eta(b) >= eta(b-1), "eta monotonicity")
            require(weight(b) > weight(b-1), "weight monotonicity")
        # Uniform asymptotic lower bound, deliberately conservative.
        require(21*eta(b) >= 22*b-21*(24+(11*b+1).bit_length()), "uniform weight asymptotic bound")
        stats["prefix_checks"] += 1
    for c in (2,6):
        missing = 8-c
        vs=pivots(81,c)
        for w in range(-20,40):
            if w%8 == missing:
                continue
            pp=1
            for b in range(81):
                require(v2(pp) >= eta(b), "integer-domain valuation")
                stats["integer_domain_checks"] += 1
                pp *= w-vs[b]
    # Actual Cauchy rows, including genuinely non-prime-field interpolation.
    for a in range(2,8):
        L=1<<a
        for i in range(a):
            R=a+1-i
            J=1<<(a-i-1)
            # Four representatives of the odd multiplier of t, where legal.
            ts = [t for t in (-3*(1<<i), -(1<<i), (1<<i), 3*(1<<i)) if -L<=t<L]
            y0s=sorted(set([0,(1<<i)-1,1<<i,(1<<(i+1))-1]))
            for t in ts:
                for y0 in y0s:
                    xs=sorted(set([x for x in range(min(L,1<<(i+2))) if ((x>>i)&1)==((y0>>i)&1)]))
                    for x in xs:
                        d0=t-y0+x
                        require(d0 and v2(d0)<=i, "crossing denominator")
                        c = 6 if i==0 or ((y0>>(i-1))&1)==0 else 2
                        for zeta in (E(0),E(1),E(0,1),E(1,1)):
                            z=(1<<(i+1))/(E(d0)+(1<<(a+1))*zeta)
                            w=z/2
                            w0=E(F(1<<i,d0))
                            require((w-w0).valuation() >= R, "prime-subring proximity")
                            if R>=3:
                                ra,rb=w.residue8()
                                require(rb==0 and ra != 8-c, "actual-row residue exclusion")
                            stats["actual_domain_checks"]+=1
                            stats["extension_domain_checks"]+=bool(zeta.b)
                            # Full separation plus all target coefficients on
                            # small cases; larger ones validate a prefix.
                            if J<=8:
                                for j in range(J):
                                    fs=features(z,j,J,c)
                                    require(sum((r*ell for r,ell in fs),E()) == 1/(1-z*j), "exact separation")
                                    stats["exact_separation_checks"]+=1
                                    for b,(rr,_) in enumerate(fs):
                                        require(rr.valuation() >= b+vf(b)+eta(b), "full target valuation")
                                        stats["target_weight_checks"]+=1
                            else:
                                rho=[2*v for v in pivots(min(J,24),c)]
                                row=E(1)
                                for b in range(min(J,24)):
                                    rr=factorial(b)*row/(1-b*z)
                                    require(rr.valuation() >= b+vf(b)+eta(b), "prefix target valuation")
                                    stats["target_weight_checks"]+=1
                                    row *= (z-rho[b])/(1-b*z)
    stats["status"]="all exact checks passed"
    stats["weight_slope"]="64/21"
    stats["meaning"]="finite algebraic checks, not proof of asymptotic theorem or SAT benchmark"
    return stats

if __name__ == "__main__":
    print(json.dumps(check(),indent=2))
