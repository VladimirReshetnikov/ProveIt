#!/usr/bin/env python3
"""Certify gamma < 1.9208 by exact, outward-rounded dyadic arithmetic.
The majorant counts unordered sums of radicals, with square roots of
positive integer squares forbidden. See the article for the height-induction
argument that turns the numerical inequality into a convergence proof.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path
BITS=1024
SCALE=1 << BITS

class I:
    __slots__=('lo','hi')
    def __init__(self,lo:int,hi:int|None=None):
        self.lo=lo; self.hi=lo if hi is None else hi
        if self.lo>self.hi: raise ValueError('Reversed interval')
    @classmethod
    def integer(cls,n:int)->I:return cls(n*SCALE)
    @classmethod
    def rational(cls,n:int,d:int)->I:
        if d<=0:raise ValueError('Denominator must be positive')
        return cls((n*SCALE)//d,-((-n*SCALE)//d))
    @staticmethod
    def convert(x:I|int)->I:return x if isinstance(x,I) else I.integer(x)
    def __add__(self,x:I|int)->I:
        x=self.convert(x);return I(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self)->I:return I(-self.hi,-self.lo)
    def __sub__(self,x:I|int)->I:return self+-self.convert(x)
    def __rsub__(self,x:I|int)->I:return self.convert(x)+-self
    def __mul__(self,x:I|int)->I:
        x=self.convert(x)
        v=[a*b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return I(min(v)//SCALE,-((-max(v))//SCALE))
    __rmul__=__mul__
    def __truediv__(self,x:I|int)->I:
        x=self.convert(x)
        if x.lo<=0:raise ValueError('Division requires positive denominator')
        ls=[(a*SCALE)//b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        us=[-((-a*SCALE)//b) for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return I(min(ls),max(us))
    def __rtruediv__(self,x:I|int)->I:return self.convert(x)/self
    def __pow__(self,n:int)->I:
        if n<0:return I.integer(1)/(self**(-n))
        a=self;out=I.integer(1)
        while n:
            if n&1:out=out*a
            a=a*a;n>>=1
        return out
    def display(self)->list[float]:return [self.lo/SCALE,self.hi/SCALE]

def mobius(n:int)->int:
    result=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;result=-result
            if n%p==0:return 0
            while n%p==0:n//=p
        p+=1
    return -result if n>1 else result

def upper_coefficients(N:int,mode:int=1)->list[int]:
    """Modes 0: sqrt(1) only; 1: integer squares; 3: stronger local rules."""
    if N<2 or mode not in (0,1,3):raise ValueError('Invalid parameters')
    u=[0]*(N+1);e=[0]*(N+1);c=[0]*(N+1);c[0]=1
    extra=[0]*(N+1)
    if mode==3:
        for m in range(1,math.isqrt(N)+1):
            for n in range(2*m*m+10*m+5,N+1,2*m+1):extra[n]+=1
    for n in range(1,N+1):
        atom=int(n==2)+u[n-1]-int(n==3)
        if mode==1 and n>3 and (n-1)%2==0:
            q=math.isqrt((n-1)//2)
            atom-=int(q*q==(n-1)//2)
        if mode==3:
            for q in range(2,math.isqrt(n-1)+1):
                if (n-1)%(q*q)==0:atom+=mobius(q)*u[(n-1)//(q*q)]
            atom-=extra[n]
        if atom<0:raise ArithmeticError('Negative atom count')
        for j in range(n,N+1,n):e[j]+=n*atom
        numerator=sum(e[k]*c[n-k] for k in range(1,n+1))
        if numerator%n:raise ArithmeticError('Euler transform lost integrality')
        c[n]=u[n]=numerator//n
    return u

def poly(coeff:list[int],x:I)->I:
    y=I.integer(0)
    for c in reversed(coeff):y=y*x+c
    return y

def P(x:I,Q:int)->I:return sum((x**(2*q*q+1) for q in range(1,Q+1)),I.integer(0))

def log_interval(r:I,J:int)->I:
    t=(1-r)/(1+r)
    s=sum((t**(2*j+1)/(2*j+1) for j in range(J)),I.integer(0))
    tail=t**(2*J+1)/((2*J+1)*(1-t*t))
    return I(-2*(s.hi+tail.hi),-2*s.lo)

def certify()->dict:
    N,K,Q,J=200,40,8,100
    r=I.rational(1250,2401)  # reciprocal of exactly 1.9208
    u=upper_coefficients(N,mode=1)
    H=I.integer(0)
    for k in range(2,K+1):
        x=r**k
        tail=(3**N)*(x**(N+1))/(1-3*x)
        bound=poly(u,x)+tail
        H=H+(x*x+x*bound-P(x,Q))/k
    tail_H=(r**(2*(K+1)))/((K+1)*(1-r*r))
    tail_H=tail_H+3*(r**(3*(K+1)))/((K+1)*(1-r**3)*(1-3*r**(K+1)))
    F=log_interval(r,J)+1+r*r-r-P(r,Q)+H+tail_H
    base_margin=1/r-1/(1-r*r)
    if F.hi>=0 or base_margin.lo<=0:
        raise ArithmeticError('The convergence inequality failed')
    # This comparison needs only the certified lower sample and local rewrite
    # majorant. It proves the first 21 terms exactly, not the remaining terms.
    known=[1,1,2,3,5,8,13,20,33,54,91,154,264,455,791,1379,
           2424,4277,7588,13513,24162,43336,77978,140683,254487,
           461409,838433,1526536]
    v=upper_coefficients(29,mode=3)
    total=0; stronger=[]
    for n in range(1,29):total+=v[n+1];stronger.append(total)
    assert stronger[:21]==known[:21]
    assert all(x>=y for x,y in zip(stronger,known))
    return {
        'upper_constant':'1.9208', 'rational_radius':'1250/2401',
        'precision_bits':BITS, 'coefficient_cutoff_N':N,
        'cycle_cutoff_K':K, 'integer_square_cutoff_Q':Q, 'log_cutoff_J':J,
        'convergence_F_interval_display':F.display(),
        'convergence_F_upper_numerator':str(F.hi),
        'convergence_F_denominator_power_of_two':BITS,
        'height_zero_margin_interval_display':base_margin.display(),
        'upper_bound_verified':True,
        'stronger_majorant_cumulative_counts':stronger,
        'first_terms_certified_exact_when_combined_with_digit_certificate':21,
    }

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    result=certify();text=json.dumps(result,indent=2)+'\n'
    print(text,end='')
    if args.output:args.output.write_text(text)
