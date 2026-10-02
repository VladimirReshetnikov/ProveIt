#!/usr/bin/env python3
"""Exact tests and outward-rounded rational interval certificates.

Python 3.10+; no third-party dependencies. Intervals have endpoints in
10**(-90) Z. Every arithmetic operation is rounded outward using integers.
Run: python verify.py
"""
from __future__ import annotations
from fractions import Fraction
from itertools import groupby
import json
from pathlib import Path

SCALE = 10**90

class Interval:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo: int, hi: int):
        assert lo <= hi
        self.lo, self.hi = lo, hi
    @staticmethod
    def value(x: int | str | Fraction) -> 'Interval':
        f = Fraction(x) * SCALE
        return Interval(f.numerator // f.denominator,
                        -((-f.numerator) // f.denominator))
    @staticmethod
    def hull(a: 'Interval', b: 'Interval') -> 'Interval':
        return Interval(min(a.lo, b.lo), max(a.hi, b.hi))
    @staticmethod
    def cast(x):
        return x if isinstance(x, Interval) else Interval.value(x)
    def __add__(self, other):
        b=self.cast(other); return Interval(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self): return Interval(-self.hi,-self.lo)
    def __sub__(self,other): return self+-self.cast(other)
    def __rsub__(self,other):return self.cast(other)+-self
    def __mul__(self,other):
        b=self.cast(other)
        p=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return Interval(min(p)//SCALE,-((-max(p))//SCALE))
    __rmul__=__mul__
    def __truediv__(self,other):
        b=self.cast(other)
        if b.lo<=0<=b.hi: raise ZeroDivisionError('interval includes zero')
        p=[Fraction(x*SCALE,y) for x in (self.lo,self.hi)
           for y in (b.lo,b.hi)]
        a,c=min(p),max(p)
        return Interval(a.numerator//a.denominator,
                        -((-c.numerator)//c.denominator))
    def __rtruediv__(self,other):return self.cast(other)/self
    def __pow__(self,n:int):
        if n<0:return 1/(self**(-n))
        ans=Interval.value(1);base=self
        while n:
            if n&1:ans=ans*base
            base=base*base;n//=2
        return ans
    def strings(self):
        def fmt(a):
            sign='-' if a<0 else '';a=abs(a)
            return f'{sign}{a//SCALE}.{a%SCALE:090d}'
        return [fmt(self.lo),fmt(self.hi)]

def certified_values(q:Interval,J:int=250):
    """Enclose U_2(q), U'_2(q), D_2(q), including the infinite tail."""
    p=[Interval.value(1)]
    for j in range(1,J+2):p.append(p[-1]*q)
    mass=p[J+1]/(1-q)
    mass_prime=(J+1)*p[J]/(1-q)+p[J+1]/(1-q)**2
    tail=mass/(1-mass)
    tail_prime=mass_prime/(1-mass)**2
    zero=Interval.value(0)
    u=Interval.hull(zero,tail)
    du=Interval.hull(zero,tail_prime)
    d=Interval.hull(zero,tail)
    for j in range(J,1,-1):
        a=p[j];da=j*p[j-1]
        den=(1-a)*(1-a-a*u)
        assert den.lo>0, f'not certified subcritical at level {j}'
        newd=a/(1-a)+d/den
        newdu=(da+du)/(1-a)**2+2*u*da/(1-a)**3
        newu=a/(1-a)+u/(1-a)**2
        u,du,d=newu,newdu,newd
    return u,du,d

def certificate():
    a='0.50596515770080666537292224451833314155847753935777'
    b='0.50596515770080666537292224451833314155847753935778'
    lo,hi=Interval.value(a),Interval.value(b)
    u,_,_=certified_values(lo);ql=1-lo*(1+u)
    u,_,_=certified_values(hi);qh=1-hi*(1+u)
    assert ql.lo>0 and qh.hi<0
    r=Interval.hull(lo,hi)
    u,du,d=certified_values(r)
    c=d/(r*(1-r)*(1+u+r*du))
    lam=1/r
    # These wider printed bounds are assertions, not floating-point guesses.
    assert c.lo>Interval.value('0.603901519061899104960307215362').hi
    assert c.hi<Interval.value('0.603901519061899104960307215364').lo
    assert lam.lo>Interval.value('1.976420677945835735314652452172').hi
    assert lam.hi<Interval.value('1.976420677945835735314652452175').lo
    return {'rho':[a,b], 'lambda':lam.strings(),'C':c.strings(),
            'Q_at_lower':ql.strings(),'Q_at_upper':qh.strings(),
            'precision_decimal_places':90,'tail_cutoff':250}

def exact_sequences(N:int=200):
    if N<1:raise ValueError('N must be positive')
    u=[0]*(N+1);d=u.copy();us={};ds={}
    for j in range(N,0,-1):
        qj=[0]*(N+1);qj[0]=1;qj[j]-=1
        for k in range(N-j+1):qj[k+j]-=u[k]
        den=qj.copy();num=d.copy()
        for k in range(N-j+1):
            den[k+j]-=qj[k];num[k+j]+=qj[k]
        nd=[];nz=[k for k in range(1,N+1) if den[k]]
        for k in range(N+1):
            nd.append(num[k]-sum(den[l]*nd[k-l] for l in nz if l<=k))
        nu=u.copy();nu[j]+=1
        if 2*j<=N:nu[2*j]-=1
        for k in range(j,N+1):
            nu[k]+=2*nu[k-j]
            if k>=2*j:nu[k]-=nu[k-2*j]
        u,d=nu,nd
        if j<=3:us[j]=u.copy();ds[j]=d.copy()
    return us,ds

def compositions(n:int):
    for mask in range(1<<(n-1)):
        a=[];v=1
        for k in range(n-1):
            if mask>>k&1:a.append(v);v=1
            else:v+=1
        a.append(v);yield a

def valley_monotone(a:list[int])->bool:
    b=[v for v,_ in groupby(a)]
    valleys=[b[k] for k in range(1,len(b)-1)
             if b[k]<b[k-1] and b[k]<b[k+1]]
    return all(x<=y for x,y in zip(valleys,valleys[1:]))

def main():
    us,ds=exact_sequences(200)
    expected_u=[0,1,2,4,8,15,27,47,79,130,209,330,512,784,1183,
                1765,2604,3804,5504,7898,11240]
    assert us[1][:len(expected_u)]==expected_u
    for n in range(1,18):
        assert sum(valley_monotone(a) for a in compositions(n))==ds[1][n]
    for n in range(1,14):
        for j in (2,3):
            assert sum(valley_monotone(a) and min(a)>=j
                       for a in compositions(n))==ds[j][n]
    assert ds[1][100]==233832578565556052089825216845
    cert=certificate()
    output={'status':'all exact checks passed','brute_force_through':17,
            'exact_coefficients_through':200,'certificate':cert,
            'd':ds[1],'unimodal_nonempty':us[1]}
    path=Path(__file__).with_name('verification.json')
    path.write_text(json.dumps(output,indent=2)+'\n')
    print('All exact coefficient, brute-force, and rational interval checks passed.')
    print('rho in',cert['rho'])
    print('lambda in',cert['lambda'])
    print('C in',cert['C'])
    print('Results:',path.name)
if __name__=='__main__':main()
