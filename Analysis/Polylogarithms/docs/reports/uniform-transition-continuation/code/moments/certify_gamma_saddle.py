#!/usr/bin/env python3
"""Exact global monotonicity certificate for the reflected log-gamma ratio.

Only integer arithmetic and Fraction are used. Every arithmetic operation
rounds OUTWARD onto the dyadic grid 2**(-100). No floating point, numerical
special-function implementation, or unproved decimal constants enter.

The script verifies positivity on [1/16,1/2]. The accompanying proof handles
the two endpoints analytically and uses reflection to cover [1/2,15/16].
"""
from fractions import Fraction as Q
from dataclasses import dataclass
import argparse,json

BITS=100
SCALE=1<<BITS
def ceildiv(a,b):return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo:int
    hi:int
    @staticmethod
    def q(x):
        x=Q(x)
        return I(x.numerator*SCALE//x.denominator,
                 ceildiv(x.numerator*SCALE,x.denominator))
    def __add__(self,other):
        other=other if isinstance(other,I) else I.q(other)
        return I(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,other):return self+-other if isinstance(other,I) else self+I.q(-other)
    def __rsub__(self,other):return I.q(other)+-self
    def __mul__(self,other):
        other=other if isinstance(other,I) else I.q(other)
        v=(self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi)
        return I(min(v)//SCALE,ceildiv(max(v),SCALE))
    __rmul__=__mul__
    def inv(self):
        assert self.lo>0
        return I(SCALE*SCALE//self.hi,ceildiv(SCALE*SCALE,self.lo))
    def __truediv__(self,other):
        return self*(other.inv() if isinstance(other,I) else I.q(other).inv())
    def __pow__(self,n):
        assert n>=0
        ans=I.q(1);base=self
        while n:
            if n&1:ans=ans*base
            base=base*base;n//=2
        return ans
    def expand(self,upper):return I(self.lo-upper.hi,self.hi+upper.hi)
    def positive_tail(self,upper):return I(self.lo,self.hi+upper.hi)

def log_small(q):
    """log(q), 1<=q<=2, using 2*atanh((q-1)/(q+1))."""
    assert 1<=q<=2
    y=I.q((q-1)/(q+1));y2=y*y;power=y;total=I.q(0);N=48
    for k in range(N):
        total=total+power/Q(2*k+1)
        power=power*y2
    remainder=2*power/(I.q(2*N+1)*(1-y2))
    return (2*total).positive_tail(remainder)

LOG2=log_small(Q(2))
def log_point(q):
    q=Q(q);k=0
    assert q>0
    while q<1:q*=2;k-=1
    while q>=2:q/=2;k+=1
    return log_small(q)+k*LOG2

def constants(N=40,K=64):
    # gamma=sum_{j>=1}(1/j-log(1+1/j)). Integral bounds on its tail,
    # using 1/(2j²)-1/(3j³) <= summand <= 1/(2j²).
    partial=I.q(sum((Q(1,j) for j in range(1,K+1)),Q(0)))-log_point(Q(K+1))
    gamma=partial+I(I.q(Q(1,2*(K+1))-Q(1,6*K*K)).lo,
                    I.q(Q(1,2*K)).hi)
    assert gamma.lo>I.q(Q(1,2)).hi and gamma.hi<I.q(Q(3,5)).lo
    zeta={}
    for n in range(2,N+1):
        partial=I.q(0)
        for k in range(1,K+1):partial=partial+I.q(Q(1,k**n))
        lower=I.q(Q(1,(n-1)*(K+1)**(n-1)))
        upper=I.q(Q(1,(n-1)*K**(n-1)))
        zeta[n]=partial+I(lower.lo,upper.hi)
    assert zeta[2].hi<I.q(2).lo
    return gamma,zeta

def polynomial(coeff,x):
    out=I.q(0)
    for c in reversed(coeff):out=out*x+c
    return out

def derivative_interval(left,right,gamma,zeta,N):
    x=I(I.q(left).lo,I.q(right).hi)
    logx=I(log_point(left).lo,log_point(right).hi)
    zero=I.q(0)
    # LogGamma(x)=-log(x)+LogGamma(1+x); all series have |x|<=1/2.
    fp=[zero,-gamma]+[((-1)**n)*zeta[n]/Q(n) for n in range(2,N+1)]
    fm=[zero,gamma]+[zeta[n]/Q(n) for n in range(2,N+1)]
    Fp=[gamma]+[((-1)**(n-1))*zeta[n] for n in range(2,N+1)]
    Fm=[gamma]+[zeta[n] for n in range(2,N+1)]
    Pp=[((-1)**n)*(n-1)*zeta[n] for n in range(2,N+1)]
    Pm=[(n-1)*zeta[n] for n in range(2,N+1)]
    one_minus=1-x
    tf=2*(x**(N+1))/(Q(N+1)*one_minus)
    tF=2*(x**N)/one_minus
    tP=2*N*(x**(N-1))/(one_minus**2)
    f_x=(-logx+polynomial(fp,x)).expand(tf)
    f_r=polynomial(fm,x).positive_tail(tf)
    F_x=(x.inv()+polynomial(Fp,x)).expand(tF)
    F_r=polynomial(Fm,x).positive_tail(tF)
    P_x=(x.inv()**2+polynomial(Pp,x)).expand(tP)
    P_r=polynomial(Pm,x).positive_tail(tP)
    assert min(f_x.lo,f_r.lo,F_x.lo,F_r.lo,P_x.lo,P_r.lo)>0
    return F_x/f_x+F_r/f_r-P_x/F_x-P_r/F_r

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--segments',type=int,default=256)
    ap.add_argument('--terms',type=int,default=40)
    ap.add_argument('--output',default=None)
    args=ap.parse_args();gamma,zeta=constants(args.terms)
    minimum=None;worst=None;bounds=[]
    for k in range(args.segments):
        left=Q(1,16)+Q(7*k,16*args.segments)
        right=Q(1,16)+Q(7*(k+1),16*args.segments)
        result=derivative_interval(left,right,gamma,zeta,args.terms)
        bounds.append(result.lo)
        if minimum is None or result.lo<minimum:minimum=result.lo;worst=[str(left),str(right)]
        assert result.lo>0, f'Failed positivity on [{left},{right}] with {result}'
    assert 4*minimum>7*SCALE, 'The claimed compact lower bound 7/4 failed.'
    data={'verified':True,'arithmetic':'outward integer dyadic intervals',
          'precision_bits':BITS,'segments':args.segments,'series_terms':args.terms,
          'gamma_bound':[str(Q(gamma.lo,SCALE)),str(Q(gamma.hi,SCALE))],
          'minimum_certified_lower_bound':str(Q(minimum,SCALE)),
          'simple_uniform_lower_bound':'7/4',
          'worst_interval':worst,'all_interval_lower_numerators':bounds,
          'endpoint_analytic_lower_bound':'176/225',
          'statement':'J prime / J is strictly positive on (0,1)'}
    if args.output:
        with open(args.output,'w') as f:json.dump(data,f,indent=2)
    print(json.dumps({k:v for k,v in data.items() if k!='all_interval_lower_numerators'},indent=2))
if __name__=='__main__':main()
