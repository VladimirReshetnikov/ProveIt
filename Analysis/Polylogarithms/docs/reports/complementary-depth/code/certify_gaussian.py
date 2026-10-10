"""Exact-rational interval enclosures for the three Gaussian triples.

The interval result is proof-backed by the analytic formulas in the article.
It is not an independent proof of a transcendental identity. No floating-point
rounding assumptions enter the rational endpoints or the width tests.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from math import factorial
from pathlib import Path
import json
import sys
if hasattr(sys,"set_int_max_str_digits"): sys.set_int_max_str_digits(100000)
import sympy as sp
from polylog_words import one_zero_formula

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q
    def __post_init__(self):
        object.__setattr__(self,'lo',Q(self.lo));object.__setattr__(self,'hi',Q(self.hi))
        if self.lo>self.hi:raise ValueError('Reversed endpoints.')
    @staticmethod
    def of(x):return x if isinstance(x,Interval) else Interval(Q(x),Q(x))
    def __add__(self,x):
        x=self.of(x);return Interval(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,x):return self+-self.of(x)
    def __rsub__(self,x):return self.of(x)+-self
    def __mul__(self,x):
        x=self.of(x);v=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
        return Interval(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=self.of(x)
        if x.lo<=0<=x.hi:raise ZeroDivisionError('Interval contains zero.')
        return self*Interval(1/x.hi,1/x.lo)
    def __pow__(self,n):
        if n<0:raise ValueError('Nonnegative integer powers only.')
        out=self.of(1)
        for _ in range(n):out=out*self
        return out
    @property
    def width(self):return self.hi-self.lo

@dataclass(frozen=True)
class ComplexInterval:
    re:Interval
    im:Interval
    @staticmethod
    def of(x):
        if isinstance(x,ComplexInterval):return x
        return ComplexInterval(Interval.of(x),Interval.of(0))
    def __add__(self,x):
        x=self.of(x);return ComplexInterval(self.re+x.re,self.im+x.im)
    __radd__=__add__
    def __neg__(self):return ComplexInterval(-self.re,-self.im)
    def __sub__(self,x):return self+-self.of(x)
    def __mul__(self,x):
        x=self.of(x)
        return ComplexInterval(self.re*x.re-self.im*x.im,self.re*x.im+self.im*x.re)
    __rmul__=__mul__
    def __pow__(self,n):
        out=self.of(1)
        for _ in range(n):out=out*self
        return out


def arctan_inverse(a:int,N=110):
    val=sum((Q((-1)**k,(2*k+1)*a**(2*k+1)) for k in range(N)),Q(0))
    term=Q((-1)**N,(2*N+1)*a**(2*N+1))
    return Interval(min(val,val+term),max(val,val+term))


def log2_interval(N=140):
    val=2*sum((Q(1,(2*k+1)*3**(2*k+1)) for k in range(N)),Q(0))
    err=Q(2,(2*N+1)*3**(2*N+1))*Q(9,8)
    return Interval(val,val+err)


def hurwitz(s:int,a:Q,N=80,M=50):
    if s<2 or a<=0:raise ValueError('Requires integer s>=2 and rational a>0.')
    x=Q(N)+a
    val=sum(((Q(n)+a)**(-s) for n in range(N)),Q(0))
    val+=x**(1-s)/(s-1)+x**(-s)/2
    last=Q(0)
    for k in range(1,M+1):
        B=sp.bernoulli(2*k);B=Q(int(B.p),int(B.q))
        rising=Q(factorial(s+2*k-2),factorial(s-1))
        last=B*rising*x**(-s-2*k+1)/factorial(2*k)
        val+=last
    # Periodic Bernoulli remainder bound: |R_M| <= |last retained term|.
    return Interval(val-abs(last),val+abs(last))


def gaussian_li(s:int,N=850):
    re=Q(0);im=Q(0);zr=Q(1);zi=Q(0)
    for n in range(1,N+1):
        zr,zi=(zr-zi)/2,(zr+zi)/2
        re+=zr/n**s;im+=zi/n**s
    # |(1+i)/2|=1/sqrt(2)<3/4; each coordinate error <= disk radius.
    err=4*Q(3,4)**(N+1)/Q(N+1)**s
    return ComplexInterval(Interval(re-err,re+err),Interval(im-err,im+err))


def directed(x:Q,rounding):
    with localcontext() as ctx:
        ctx.prec=115;ctx.rounding=rounding
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def encode(iv:Interval):
    return dict(lower_numerator=str(iv.lo.numerator),lower_denominator=str(iv.lo.denominator),
                upper_numerator=str(iv.hi.numerator),upper_denominator=str(iv.hi.denominator),
                lower_decimal=directed(iv.lo,ROUND_FLOOR),
                upper_decimal=directed(iv.hi,ROUND_CEILING),
                width_upper_decimal=directed(iv.width,ROUND_CEILING))


def main():
    pi=16*arctan_inverse(5)-4*arctan_inverse(239)
    l=log2_interval();G=(hurwitz(2,Q(1,4))-hurwitz(2,Q(3,4)))/16
    z3=hurwitz(3,Q(1));zetas={2:pi**2/6,3:z3,4:pi**4/90}
    L=ComplexInterval(-l/2,pi/4);atoms={k:gaussian_li(k) for k in range(1,5)}
    la3=atoms[3].im;la4=atoms[4].im
    printed=[la4+la3*l/2-G*(pi**2-4*l**2)/32-pi*(8*l**3+105*z3)/768,
      -3*la4-la3*l+G*(pi**2-4*l**2)/32-3*pi**3*l/256+pi*(2*l**3+67*z3)/128,
      3*la4+la3*l/2+5*pi**3*l/192-163*pi*z3/256]
    rows=[]
    for (a,b),candidate in zip([(0,2),(1,1),(2,0)],printed):
        total=ComplexInterval.of(0)
        for (j,S,T),c in one_zero_formula(a,b).items():
            term=(L**j)*c
            if S:term=term*atoms[S[0]]
            if T:term=term*zetas[T[0]]
            total=total+term
        residual=total.im-candidate
        assert residual.lo<=0<=residual.hi
        assert total.re.width<Q(1,10**90)
        assert total.im.width<Q(1,10**90)
        rows.append(dict(a=a,b=b,real_part=encode(total.re),imaginary_part=encode(total.im),
                         printed_identity_residual=encode(residual)))
    report=dict(status='PASS',endpoint_arithmetic='fractions.Fraction only',
        enclosure_width_less_than='1e-90 for each real and imaginary target component',
        interpretation='Enclosures use analytically proved identities; overlap is not itself a proof of equality.',
        parameters=dict(polylog_terms=850,polylog_radius_majorant='3/4',
                        hurwitz_N=80,hurwitz_M=50,arctan_terms=110,log2_terms=140),
        triples=rows)
    root=Path(__file__).resolve().parents[1]
    (root/'certificates'/'gaussian_intervals.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],report['enclosure_width_less_than'])
    for row in rows:
        print(row['a'],row['b'],row['imaginary_part']['lower_decimal'][:65],
              row['imaginary_part']['width_upper_decimal'])

if __name__=='__main__':main()
