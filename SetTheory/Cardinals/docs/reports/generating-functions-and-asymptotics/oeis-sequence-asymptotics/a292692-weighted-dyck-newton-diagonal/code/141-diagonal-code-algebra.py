#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Exact rational-function and quadratic-field algebra; Python standard library only."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb


def require(condition, message):
    if not condition: raise ArithmeticError(message)


def trim(p):
    p = list(map(F,p))
    while len(p)>1 and not p[-1]: p.pop()
    return p


def padd(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a): c[i]+=v
    for i,v in enumerate(b): c[i]+=v
    return trim(c)


def pmul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b): c[i+j]+=v*w
    return trim(c)


def pscale(a,c): return trim([v*c for v in a])


def pdiv(a,b):
    a,b=trim(a),trim(b)
    require(b != [0], 'polynomial division by zero')
    q=[F(0)]*max(1,len(a)-len(b)+1)
    while a != [0] and len(a)>=len(b):
        j=len(a)-len(b); c=a[-1]/b[-1];q[j]=c
        a=padd(a,[F(0)]*j+pscale(b,-c))
    return trim(q),a


def pgcd(a,b):
    while b != [0]: a,b=b,pdiv(a,b)[1]
    return pscale(a,1/a[-1])


class RationalFunction:
    def __init__(self,numerator=0,denominator=1):
        n=trim(numerator if isinstance(numerator,(list,tuple)) else [numerator])
        d=trim(denominator if isinstance(denominator,(list,tuple)) else [denominator])
        require(d != [0], 'zero rational-function denominator')
        gcd=pgcd(n,d);n=pdiv(n,gcd)[0];d=pdiv(d,gcd)[0]
        lead=d[-1];self.n=pscale(n,1/lead);self.d=pscale(d,1/lead)
    @staticmethod
    def cast(x): return x if isinstance(x,RationalFunction) else RationalFunction(x)
    def __add__(self,other):
        other=self.cast(other)
        return RationalFunction(padd(pmul(self.n,other.d),pmul(other.n,self.d)),pmul(self.d,other.d))
    __radd__=__add__
    def __neg__(self): return RationalFunction(pscale(self.n,-1),self.d)
    def __sub__(self,other): return self+-self.cast(other)
    def __rsub__(self,other): return self.cast(other)+-self
    def __mul__(self,other):
        other=self.cast(other);return RationalFunction(pmul(self.n,other.n),pmul(self.d,other.d))
    __rmul__=__mul__
    def __truediv__(self,other):
        other=self.cast(other);return RationalFunction(pmul(self.n,other.d),pmul(self.d,other.n))
    def __rtruediv__(self,other): return self.cast(other)/self
    def __pow__(self,n):
        require(type(n) is int and n>=0,'nonnegative integer power required')
        out=RationalFunction(1)
        for _ in range(n): out=out*self
        return out
    def derivative(self):
        dn=[i*v for i,v in enumerate(self.n)][1:] or [F(0)]
        dd=[i*v for i,v in enumerate(self.d)][1:] or [F(0)]
        return RationalFunction(padd(pmul(dn,self.d),pscale(pmul(self.n,dd),-1)),pmul(self.d,self.d))
    def __eq__(self,other):
        other=self.cast(other);return self.n==other.n and self.d==other.d
    def encoded(self):return {'numerator':[str(v) for v in self.n], 'denominator':[str(v) for v in self.d]}


class Quadratic:
    # a + b sqrt(17), with exact rational a,b.
    def __init__(self,a=0,b=0): self.a=F(a);self.b=F(b)
    @staticmethod
    def cast(x): return x if isinstance(x,Quadratic) else Quadratic(x)
    def __add__(self,other):
        other=self.cast(other);return Quadratic(self.a+other.a,self.b+other.b)
    __radd__=__add__
    def __neg__(self): return Quadratic(-self.a,-self.b)
    def __sub__(self,other):return self+-self.cast(other)
    def __rsub__(self,other):return self.cast(other)+-self
    def __mul__(self,other):
        other=self.cast(other);return Quadratic(self.a*other.a+17*self.b*other.b,self.a*other.b+self.b*other.a)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=self.cast(other);d=other.a*other.a-17*other.b*other.b
        return self*Quadratic(other.a/d,-other.b/d)
    def __rtruediv__(self,other):return self.cast(other)/self
    def __pow__(self,n):
        out=Quadratic(1)
        for _ in range(n):out=out*self
        return out
    def __eq__(self,other):
        other=self.cast(other);return self.a==other.a and self.b==other.b
    def encoded(self):return [str(self.a),str(self.b)]


def evaluate(function,x):
    def poly(p):
        out=Quadratic(0)
        for a in reversed(p):out=out*x+a
        return out
    return poly(function.n)/poly(function.d)


def run():
    s=RationalFunction([0,1]);t=1-s*s;alpha=2*s*s/(1+s);mu=1/alpha
    B=t*(s+2)/(4*s**4);f=1/s
    def D(g):return -t/(2*s)*g.derivative()
    E=D(f)/f-D(B)/(2*B)
    expected_E=-(s**3+s+4)/(4*s*s*(s+2))
    require(E==expected_E,'saddle amplitude drift')
    c1=-D(D(f))/(2*f*B)+D(f)*D(B)/(2*f*B**2)+D(D(B))/(8*B**2)-5*D(B)**2/(24*B**3)
    expected_c1=(s**6-7*s**5-5*s**4+32*s**3+32*s*s-9*s-8)/(12*(s-1)*(s+1)*(s+2)**3)
    require(c1==expected_c1,'first Gaussian coefficient')
    # sqrt(t) times the first and second endpoint moments eliminates roots.
    # If M_j=sqrt(t) sum ell^j gamma_ell s^(2ell), Euler
    # differentiation gives M_(j+1)=(s/2)M_j' + s^2 M_j/(2t).
    M0=RationalFunction(1)
    moment=lambda M:s/2*M.derivative()+s*s/(2*t)*M
    L1=moment(M0);L2=moment(L1)
    require(L1==s*s/(2*t) and L2==L1+3*s**4/(4*t*t),'endpoint moments by Euler differentiation')
    K=L2/2-L1+mu*(L2-F(3,2)*s*L2+s*L1-E/B*(1-mu*s)*L1-
                        ((1-mu*s)**2*L2+mu**2*s*(1-s)*L1)/(2*B))
    J=(alpha-s)*L1
    source=s*s/(2*t)
    r1=-K+(1+s)**2*J/(2*(s+2)*t)-source
    expected_r1=(s**4+6*s**3+7*s*s+3*s+4)/(4*(s-1)*(s+1)*(s+2)**2)
    require(r1==expected_r1,'first contraction residual')
    shifted=[]
    for ell in range(5):
        for r in range(ell+1):
            b=ell-mu*r
            D1=(-D(D(f))/(2*f)-D(f)/f*b+(r*B-b*b)/2)/B+\
                (D(f)/f+b)*D(B)/(2*B**2)+D(D(B))/(8*B**2)-5*D(B)**2/(24*B**3)
            shift=RationalFunction(F(r,2))
            shift=shift-E*b/B-b*b/(2*B)
            require(D1-c1==shift,'shifted Gaussian coefficient')
            # Product of Newton, double-factorial, falling-factorial, saddle,
            # and (N-ell)/N corrections, all at the original saddle.
            combined=mu*(ell-r)*F(2*ell-r,2)+F(ell*ell,2)-mu*F(r*(r-1),2)+mu*shift-ell
            kappa=F(ell*ell,2)-ell+mu*(ell*ell-F(3,2)*ell*r+r-E*b/B-b*b/(2*B))
            require(combined==kappa,'principal endpoint first correction')
            shifted.append({'ell':ell,'r':r,'coefficient':shift.encoded(),'kappa':kappa.encoded()})
    # First two coefficients of the exact Newton multiplication polynomial.
    def shift_minus_one(p):
        q=[F(0)]*len(p)
        for i,v in enumerate(p):
            for j in range(i+1):q[j]+=v*comb(i,j)*(-1)**(i-j)
        return trim(q)
    @lru_cache(None)
    def op(ell,r):
        if r<0 or r>ell:return (F(0),)
        if ell==0:return (F(1),)
        return tuple(padd(pmul([2*ell-1,1],op(ell-1,r)),shift_minus_one(op(ell-1,r-1))))
    op_rows=[]
    for ell in range(1,13):
        for r in range(ell+1):
            p=op(ell,r);degree=ell-r;lead=p[degree];next_=p[degree-1] if degree else F(0)
            require(lead==comb(ell,r),'operator leading term')
            require(next_==comb(ell,r)*degree*F(2*ell-r,2),'operator first term')
            op_rows.append({'ell':ell,'r':r,'polynomial':[str(v) for v in p],
                            'leading':str(lead),'next':str(next_)})
    s0=Quadratic(F(1,8),F(1,8));t0=1-s0*s0;B0=evaluate(B,s0)
    d=16*((1-s0)/s0)/(t0*t0)
    Cpi_squared=4*t0/(s0*s0*B0)
    require(evaluate(alpha,s0)==F(1,2),'diagonal saddle')
    require(d==Quadratic(F(-107,4),F(51,4)),'exponential base')
    require(Cpi_squared==Quadratic(2,F(2,17)),'amplitude squared times pi cubed')
    factorial_correction=F(1,48)-F(1,24)-F(2,12)
    require(factorial_correction==F(-3,16),'Stirling first correction')
    saddle_correction=evaluate(c1,s0);ratio_correction=evaluate(r1,s0)/2
    b1=factorial_correction+saddle_correction+ratio_correction
    require(b1==Quadratic(F(-989,2176),F(-907,36992)),'diagonal first correction')
    inverse_c1=b1+F(1,12)
    # With y=1/x0 and g=log(d*x0), delta=-c1*y/g.
    # The y coefficients of Phi(x0+delta)-L+c1/(x0+delta) cancel.
    require(-inverse_c1+inverse_c1==0,'inverse order-y cancellation')
    # The y^3 coefficient is c1^2/g + c1^2/(2g^2).
    return {'field_radicand':17,'constants':{'s':s0.encoded(),'t':t0.encoded(),'B':B0.encoded(),
            'd':d.encoded(),'pi_cubed_C_squared':Cpi_squared.encoded(),'b1':b1.encoded()},
            'rational_functions':{'E':E.encoded(),'c1':c1.encoded(),'r1':r1.encoded(),
                                   'scaled_L1':L1.encoded(),'scaled_L2':L2.encoded(),
                                   'scaled_K':K.encoded(),'scaled_J':J.encoded(),'source':source.encoded()},
            'diagonal_correction':{'factorial':str(factorial_correction),'saddle':saddle_correction.encoded(),
                                   'ratio':ratio_correction.encoded(),'total':b1.encoded()},
            'inverse':{'c1':inverse_c1.encoded(),'cancelled_linear':Quadratic(0).encoded(),
                       'cubic_inverse_log':(inverse_c1**2).encoded(),
                       'cubic_inverse_log_squared':(inverse_c1**2/2).encoded()},
            'shifted_saddles':shifted,'operator_coefficients':op_rows}


if __name__ == '__main__':
    import json
    print(json.dumps(run(),sort_keys=True,indent=2,allow_nan=False))
