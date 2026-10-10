#!/usr/bin/env python3
"""Exact-rational proximity certificates for the conjectural S6 and S8 identities.

The direct Gaussian bound is proved in the new article, Proposition
"Direct one-sided Euler enclosures" (sections/gaussian_candidate.tex).
The alternative signed-kernel bounds are proved in the pinned manuscript
cc34f73596336f2466d9754cb0f3635bd2bedade, chapter 05-signed-kernels.tex:
signed:thm:euler-certificate, signed:prop:euler-weights, signed:prop:S-euler,
and signed:eq:log2-bound. No floating-point number enters the computation.
This proves proximity of the two sides, NOT equality.
"""
from fractions import Fraction as Q
from math import lcm
import json
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(1000000)
HERE = Path(__file__).resolve().parents[1]/"results"
S6_VECTOR = [485683200,-665395200,-36864000,401080320,
             -258247,11750400,109347840,971366400]
S8_VECTOR = [-10974719508480,15125246115840,816174858240,
             -394908401664,-5770366156800,633846205,-44376595200,
             -518730670080,-2998569369600,-21949439016960]


class Interval:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = Q(lo), Q(lo if hi is None else hi)
        assert self.lo <= self.hi
    def __add__(self, other):
        if not isinstance(other,Interval): other=Interval(other)
        return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __mul__(self, other):
        if not isinstance(other,Interval): other=Interval(other)
        corners=[self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi]
        return Interval(min(corners),max(corners))
    __rmul__=__mul__
    def __pow__(self, n):
        assert n>=0 and self.lo>=0
        return Interval(self.lo**n,self.hi**n)
    def __truediv__(self,n):
        return self*Q(1,n)


class ExactEuler:
    def __init__(self,N,gaussian_bound='source'):
        self.N=N
        self.gaussian_bound=gaussian_bound
        self.L=1
        for j in range(1,2*N+1): self.L=lcm(self.L,j)
        c=1
        tail=(1<<N)-1
        self.weights=[]
        for n in range(N):
            self.weights.append((-1 if n%2 else 1)*tail)
            c=c*(N-n)//(n+1)
            tail-=c
        assert tail==0
        self.scale=1<<N
    def gaussian(self,a,b):
        numerator=0
        harmonic=0
        for n,weight in enumerate(self.weights):
            if n:
                harmonic+=(self.L//(2*n-1))**b+(self.L//(2*n))**b
            numerator+=weight*harmonic*(self.L//(2*n+1))**a
        E=Q(numerator,self.scale*self.L**(a+b))
        if self.gaussian_bound=='source':
            C=Q(1) if b==1 else Q(b,b-1)
        elif self.gaussian_bound=='direct':
            C=Q(self.N+1,3**a)*(1+Q(1,2**b))
        else:
            raise ValueError('unknown Gaussian bound')
        return Interval(E-C/self.scale,E)
    def mixed(self,p):
        numerator=0
        harmonic=0
        for n,weight in enumerate(self.weights):
            if n: harmonic+=self.L//n
            numerator+=weight*harmonic*(self.L//(2*n+1))**p
        E=Q(numerator,self.scale*self.L**(p+1))
        return Interval(E-Q(self.N+1,3**p*self.scale),E)
    def depth_one(self,s,odd):
        numerator=sum(weight*(self.L//(2*n+1 if odd else n+1))**s
                      for n,weight in enumerate(self.weights))
        E=Q(numerator,self.scale*self.L**s)
        return Interval(E,E+Q(1,self.scale))
    def beta(self,s): return self.depth_one(s,True)
    def zeta(self,s): return self.depth_one(s,False)*Q(2**(s-1),2**(s-1)-1)


def atan_reciprocal(q,N):
    s=sum((Q((-1)**n,(2*n+1)*q**(2*n+1)) for n in range(N)),Q())
    t=Q(1,(2*N+1)*q**(2*N+1))
    return Interval(s,s+t) if N%2==0 else Interval(s-t,s)


def pi_interval(N):
    return 16*atan_reciprocal(5,N)+(-4)*atan_reciprocal(239,N)


def log2_interval(N):
    s=2*sum((Q(1,(2*n+1)*3**(2*n+1)) for n in range(N)),Q())
    return Interval(s,s+Q(9,4*(2*N+1)*3**(2*N+1)))


def decimal_string(n, digits):
    sign='-' if n<0 else ''
    raw=str(abs(n)).zfill(digits+1)
    return sign+raw[:-digits]+'.'+raw[-digits:]


def describe(iv,digits=370):
    scale=10**digits
    lower=(iv.lo.numerator*scale)//iv.lo.denominator
    upper=-((-iv.hi.numerator*scale)//iv.hi.denominator)
    return {'lower_decimal':decimal_string(lower,digits),
            'upper_decimal':decimal_string(upper,digits),
            'exact_lower':[str(iv.lo.numerator),str(iv.lo.denominator)],
            'exact_upper':[str(iv.hi.numerator),str(iv.hi.denominator)]}


def normalized_difference(vals,vector):
    return sum((v*Q(c,vector[0]) for v,c in zip(vals,vector)),Interval(0))


def run(N=1100,gaussian_bound='source'):
    start=time.time()
    e=ExactEuler(N,gaussian_bound)
    # More than enough accuracy in the independent elementary constants.
    pi=pi_interval(300)
    log2=log2_interval(400)
    beta={s:e.beta(s) for s in [2,4,6,8]}
    zeta={s:e.zeta(s) for s in [3,5,7]}
    vals6=[e.mixed(6)]+[e.gaussian(a,b) for a,b in [(6,1),(4,3),(2,5)]]
    vals6 += [pi**7,beta[2]*zeta[5],beta[4]*zeta[3],beta[6]*log2]
    vals8=[e.mixed(8)]+[e.gaussian(a,b) for a,b in [(8,1),(6,3),(4,5),(2,7)]]
    vals8 += [pi**9,beta[2]*zeta[7],beta[4]*zeta[5],beta[6]*zeta[3],beta[8]*log2]
    report={'status':'Certified proximity only; both identities remain conjectural.',
            'source_commit':'cc34f73596336f2466d9754cb0f3635bd2bedade',
            'N':N,'gaussian_bound':gaussian_bound,
            'pi_arctangent_terms_each':300,'log2_terms':400,
            'arithmetic':'Python exact integers and fractions.Fraction throughout'}
    for name,vals,vector in [('S6',vals6,S6_VECTOR),('S8',vals8,S8_VECTOR)]:
        residual=sum((v*c for v,c in zip(vals,vector)),Interval(0))
        normalized=normalized_difference(vals,vector)
        assert normalized.lo<=0<=normalized.hi
        exponent=330 if gaussian_bound=='source' else 355
        bound=Q(1,10**exponent)
        assert -bound<=normalized.lo and normalized.hi<=bound
        report[name]={'vector':vector,'normalized_difference':describe(normalized),
                      'integer_residual':describe(residual),
                      'proved_enclosure':f'[-10^-{exponent},10^-{exponent}]',
                      'basket_values':[describe(v) for v in vals]}
        print(name,f'normalized difference within +/- 1e-{exponent} (exact, {gaussian_bound} bound)',flush=True)
    report['elapsed_seconds']=time.time()-start
    filename='s6_s8_interval_certificate.json' if gaussian_bound=='source' else 's6_s8_direct_interval_certificate.json'
    (HERE/filename).write_text(json.dumps(report,indent=2)+'\n')
    print('Finished in %.3f s'%report['elapsed_seconds'],flush=True)


if __name__=='__main__':
    run()
    run(N=1200,gaussian_bound='direct')
