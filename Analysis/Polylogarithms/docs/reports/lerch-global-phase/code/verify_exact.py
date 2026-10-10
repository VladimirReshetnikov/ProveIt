#!/usr/bin/env python3
"""Proof-bearing rational certificates for the index-three Lerch phase diagram.

Python standard library only. No floating-point arithmetic is used to decide
any sign. Intervals have integer endpoints on a fixed decimal grid. The script
recomputes every logarithm and every remainder from explicit analytic bounds.
See the article for the mathematical implications and Euler--Maclaurin proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, comb
from pathlib import Path
import argparse
import json

SCALE = 10**60
LOG_TERMS = 68

def ceildiv(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError('positive denominator required')
    return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo: int
    hi: int
    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError('reversed interval')
    @staticmethod
    def of(x: int | Q | 'I') -> 'I':
        if isinstance(x, I): return x
        q = Q(x)
        return I((q.numerator*SCALE)//q.denominator,
                 ceildiv(q.numerator*SCALE, q.denominator))
    @staticmethod
    def bounds(a: Q, b: Q) -> 'I':
        return I(I.of(a).lo, I.of(b).hi)
    def __add__(self, other):
        y=I.of(other); return I(self.lo+y.lo, self.hi+y.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,other): return self+-I.of(other)
    def __rsub__(self,other): return I.of(other)+-self
    def __mul__(self,other):
        y=I.of(other)
        v=[self.lo*y.lo,self.lo*y.hi,self.hi*y.lo,self.hi*y.hi]
        return I(min(v)//SCALE,ceildiv(max(v),SCALE))
    __rmul__=__mul__
    def reciprocal(self):
        if self.lo <= 0 <= self.hi: raise ZeroDivisionError('interval contains zero')
        if self.hi < 0: return -(-self).reciprocal()
        return I(SCALE*SCALE//self.hi,ceildiv(SCALE*SCALE,self.lo))
    def __truediv__(self,other): return self*I.of(other).reciprocal()
    def __rtruediv__(self,other): return I.of(other)*self.reciprocal()
    def __pow__(self,n:int):
        if n<0:return (self.reciprocal())**(-n)
        out=I.of(1); base=self
        while n:
            if n&1:out=out*base
            base=base*base;n//=2
        return out
    def positive(self): return self.lo>0
    def negative(self): return self.hi<0
    def record(self):
        return {'lower_numerator':str(self.lo), 'upper_numerator':str(self.hi),
                'denominator':str(SCALE), 'display':self.display()}
    def display(self, digits:int=16):
        den=10**(60-digits)
        def fixed(v:int):
            sign='-' if v<0 else ''; v=abs(v)
            return f'{sign}{v//(10**digits)}.{v%(10**digits):0{digits}d}'
        return '['+fixed(self.lo//den)+', '+fixed(ceildiv(self.hi,den))+']'

@lru_cache(None)
def log_reduced(q:Q) -> I:
    """Log of 1 <= q <= 2, using atanh and a rational tail bound."""
    if not 1<=q<=2:raise ValueError('range reduction failure')
    z=I.of((q-1)/(q+1)); z2=z*z; term=z; ans=I.of(0)
    for j in range(LOG_TERMS):
        ans += term*Q(2,2*j+1); term*=z2
    # Since 0<=z<=1/3, the exact omitted series is in [0,R].
    R=Q(2,1)*Q(1,3)**(2*LOG_TERMS+1)/((2*LOG_TERMS+1)*(1-Q(1,9)))
    return I(ans.lo,ans.hi+I.of(R).hi)

@lru_cache(None)
def log_q(q:Q) -> I:
    q=Q(q)
    if q<=0:raise ValueError('logarithm requires positivity')
    k=0
    while q<1:q*=2;k-=1
    while q>2:q/=2;k+=1
    return log_reduced(q)+k*log_reduced(Q(2))

def log_i(x:I) -> I:
    if x.lo<=0:raise ValueError('log interval must be positive')
    return I(log_q(Q(x.lo,SCALE)).lo,log_q(Q(x.hi,SCALE)).hi)

def poly_eval(coeff:list[int|Q],x:I)->I:
    out=I.of(0)
    for c in reversed(coeff):out=out*x+c
    return out

def poly_derivative_step(p:list[int|Q], exponent:int)->list[int|Q]:
    # d/dx [x^{-exponent} P(log x)] = x^{-exponent-1}(P'-exponent P).
    return [(j+1)*(p[j+1] if j+1<len(p) else 0)-exponent*p[j]
            for j in range(len(p))]

P0=[0,0,3,-1]

def f(x:I)->I:
    return poly_eval(P0,log_i(x))/x**2

def df(x:I)->I:
    return poly_eval([0,6,-9,2],log_i(x))/x**3

@lru_cache(None)
def bernoulli(n:int)->Q:
    if n==0:return Q(1)
    return -sum(Q(comb(n+1,j))*bernoulli(j) for j in range(n))/Q(n+1)

def log_integral(b:I, exponent:int, power:int)->I:
    """Exact formula enclosing integral_b^infinity log(x)^power/x^exponent dx."""
    if exponent<=1 or b.lo<SCALE:raise ValueError('invalid tail parameters')
    L=log_i(b); out=I.of(0); v=exponent-1
    for j in range(power+1):
        out+=Q(factorial(power),factorial(power-j)*v**(j+1))*L**(power-j)
    return out/b**(exponent-1)

def em_anchor(a:Q,N:int=32,p:int=6)->tuple[I,I]:
    """Euler--Maclaurin enclosure of sum_{m>=0} f(a+m)."""
    ans=sum((f(I.of(a+m)) for m in range(N)), I.of(0))
    b=I.of(a+N);L=log_i(b)
    ans+=-L**3/b+f(b)/2
    pol=P0[:]
    polys=[pol]
    for r in range(2*p):
        pol=poly_derivative_step(pol,2+r);polys.append(pol)
    for j in range(1,p+1):
        deriv=poly_eval(polys[2*j-1],L)/b**(2*j+1)
        ans-=Q(bernoulli(2*j),factorial(2*j))*deriv
    integral=sum((abs(c)*log_integral(b,2+2*p,j)
                  for j,c in enumerate(polys[2*p])), I.of(0))
    radius=Q(abs(bernoulli(2*p)),factorial(2*p))*integral
    return I(ans.lo-radius.hi,ans.hi+radius.hi),radius

def derivative_tail(b:Q)->I:
    # df(x) <= 2 log(x)^3/x^3 for x >= b. This majorant decreases.
    B=I.of(b); L=log_q(b)
    return 2*L**3/B**3+2*log_integral(B,3,3)

def verify_derivative(cells:int=128,M:int=64)->tuple[list[dict],I]:
    left,right=Q(9,5),Q(11,4);r=Q(9,10)
    tail=derivative_tail(left+M)
    rows=[]
    for j in range(cells):
        a=left+(right-left)*Q(j,cells)
        b=left+(right-left)*Q(j+1,cells)
        A=I.bounds(a,b)
        upper=I.of(0)
        for m in range(M):
            v=df(A+m)
            # If v.hi is nonpositive, rho^m >= (9/10)^m gives the upper bound.
            # Otherwise rho^m <=1 and rho^m*df <= max(v.hi,0)=v.hi.
            u=I(v.hi,v.hi)
            upper+=u*(r**m if v.hi<=0 else 1)
        upper+=tail
        assert upper.hi<0, f'derivative certificate failed on [{a},{b}]: {upper.display()}'
        rows.append({'a':str(a),'b':str(b),'upper_bound_numerator':str(upper.hi),
                     'denominator':str(SCALE),'display_upper':upper.display()})
    return rows,tail

def run()->dict:
    assert Q(163,60)**3>20
    # e = sum 1/j! < 163/60 + (1/720)/(1-1/7) < 11/4.
    assert Q(163,60)+Q(1,720)/(1-Q(1,7))<Q(11,4)
    low_margin=Q(6,121)-Q(33,160)*Q(9,10)**18
    assert low_margin>0
    anchors=[]
    for a,sgn in [(Q(4,5),1),(Q(1),-1),(Q(3,2),1),(Q(9,5),1)]:
        value,rad=em_anchor(a)
        assert value.positive() if sgn>0 else value.negative()
        anchors.append({'a':str(a),'F':value.record(),'EM_radius':rad.record(),'sign':sgn})
    rows,tail=verify_derivative()
    largest=max(int(v['upper_bound_numerator']) for v in rows)
    # These coarse outward bounds can be read directly in the article.
    assert largest < -(SCALE//40) # theorem: the complete strip is below -1/40
    return {'schema':'proveit.lerch-global-phase.exact-certificate.v1',
            'arithmetic':'integer fixed-point interval arithmetic',
            'scale':str(SCALE),'log_terms':LOG_TERMS,'EM_N':32,'EM_p':6,
            'anchors':anchors,'low_rho_margin':str(low_margin),
            'derivative':{'rho_interval':['9/10','1'], 'a_interval':['9/5','11/4'],
                          'cells':128,'summands':64, 'tail':tail.record(),
                          'largest_upper_bound':I(largest,largest).record(),'rows':rows},
            'status':'PASS'}

def main()->None:
    if not __debug__:
        raise RuntimeError('Exact verification requires assertions; do not use Python -O or -OO.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'certificates'/'exact.json')
    args=p.parse_args()
    data=run();args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    for a in data['anchors']:print('F('+a['a']+',1):',a['F']['display'])
    print('Uniform derivative maximum upper bound:',data['derivative']['largest_upper_bound']['display'])
    print('All proof-bearing checks: PASS')

if __name__=='__main__':main()
