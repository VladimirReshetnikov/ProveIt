#!/usr/bin/env python3
"""Rigorous (subject to Python Decimal's documented correct rounding) RH-based
zeta zero-count demonstration. All algebra uses outward fixed-point intervals;
only sqrt/log/exp rely on correctly rounded Decimal elementary functions.
Analytic series tails are bounded in the accompanying paper.
"""
from fractions import Fraction as Q
from decimal import Decimal, localcontext
from math import comb, ceil, floor
import json
from pathlib import Path
from zero_count import nodes, bracket_intervals

P=100
S=10**P

def up(a,b): return -((-a)//b)

class I:
    __slots__=('l','h')
    def __init__(self,x=0):
        x=Q(x); self.l=x.numerator*S//x.denominator; self.h=up(x.numerator*S,x.denominator)
    @classmethod
    def ends(cls,l,h):
        assert l<=h
        r=object.__new__(cls);r.l=l;r.h=h;return r
    @staticmethod
    def asI(x): return x if isinstance(x,I) else I(x)
    def __add__(self,x):
        x=self.asI(x);return I.ends(self.l+x.l,self.h+x.h)
    __radd__=__add__
    def __neg__(self): return I.ends(-self.h,-self.l)
    def __sub__(self,x): return self+-self.asI(x)
    def __rsub__(self,x): return self.asI(x)+-self
    def __mul__(self,x):
        x=self.asI(x);p=[self.l*x.l,self.l*x.h,self.h*x.l,self.h*x.h]
        return I.ends(min(p)//S,up(max(p),S))
    __rmul__=__mul__
    def inv(self):
        assert self.l>0 or self.h<0, 'division interval contains zero'
        return I.ends(S*S//self.h,up(S*S,self.l))
    def __truediv__(self,x):
        x=self.asI(x);assert x.l>0 or x.h<0
        pairs=[(S*a,b) for a in (self.l,self.h) for b in (x.l,x.h)]
        return I.ends(min(a//b for a,b in pairs),max(up(a,b) for a,b in pairs))
    def __rtruediv__(self,x): return self.asI(x)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        y=I(1);x=self
        while n:
            if n&1:y=y*x
            n//=2
            if n:x=x*x
        return y
    def elem(self,name):
        # Decimal constructor from scientific string is exact; elementary
        # operation rounds to nearest, then one neighboring decimal in each
        # direction encloses the exact value (all three are monotone).
        if name in ('ln','sqrt'): assert self.l>0
        with localcontext() as ctx:
            ctx.prec=P+12
            l=getattr(Decimal(f'{self.l}e-{P}'),name)().next_minus()
            h=getattr(Decimal(f'{self.h}e-{P}'),name)().next_plus()
        return I.ends(I(Q(l)).l,I(Q(h)).h)
    def log(self): return self.elem('ln')
    def exp(self): return self.elem('exp')
    def sqrt(self): return self.elem('sqrt')
    def expand(self,r):
        r=self.asI(r);assert r.h>=0
        return I.ends(self.l-r.h,self.h+r.h)
    def bounds(self):return Q(self.l,S),Q(self.h,S)

def atan_inverse(k,n=90):
    z=Q(1,k);v=sum((-1)**j*z**(2*j+1)/ (2*j+1) for j in range(n))
    return I(v).expand(z**(2*n+1)/(2*n+1))

PI=16*atan_inverse(5)-4*atan_inverse(239)

def bernoullis(n):
    B=[Q(1)]
    for m in range(1,n+1): B.append(-sum(comb(m+1,j)*B[j] for j in range(m))/(m+1))
    return B

ORDER=50
B=bernoullis(2*ORDER+2)

def digamma(x):
    shift=100; z=x+shift
    v=z.log()-1/(2*z)
    z2=z*z;power=z2
    for r in range(1,ORDER+1):
        v-=I(B[2*r]/(2*r))/power
        power*=z2
    v=v.expand(I(abs(B[2*ORDER+2])/(2*ORDER+2))/power)
    return v-sum(1/(x+j) for j in range(shift))

N=380
# Precompute the finite Euler transform's exact dyadic coefficients.
weights=[0]*N
for n in range(N):
    for k in range(n+1):weights[k]+=comb(n,k)<<(N-1-n)
weights=[I(Q((-1)**k*w,2**N)) for k,w in enumerate(weights)]
logs=[I(k+1).log() for k in range(N)]

def zeta_logderiv(s):
    eta=I(0);der=I(0)
    for w,l in zip(weights,logs):
        v=w*(-s*l).exp();eta+=v;der-=l*v
    eta=eta.expand(Q(1,2**N))
    der=der.expand(2*(s+1/(s-1))*I(Q(1,2**N)))
    z=( (1-s)*logs[1]).exp()
    return der/eta-logs[1]*z/(1-z)

def value(a,x):
    r=x.sqrt();s=I(Q(1,2))+r
    return a*(1/s+1/(s-1)-PI.log()/2+digamma(s/2)/2+zeta_logderiv(s))/r

def outward(q,upper,places=12):
    u=10**places;v=q*u
    m=ceil(v) if upper else floor(v)
    sign='-' if m<0 else '';m=abs(m)
    return f'{sign}{m//u}.{m%u:0{places}d}'

def main():
    a=64;n=16;tau=Q(1,2);km=7;kp=10;ds=nodes(n)
    M=value(a,I(a));vals=[value(a,I(a*(1+d))) for d in ds]
    L,U=bracket_intervals(ds,tau,km,kp,M.bounds(),[v.bounds() for v in vals])
    assert ceil(L)<=0 and floor(U)==0
    print('Certified RH-based zeta count for |Im rho| <= 8: 0')
    print('Outward count bracket:',outward(L,False),outward(U,True))
    print('Maximum input interval width:',max(v.h-v.l for v in [M]+vals),'* 10^-100')
    # Exact endpoints serialized as scaled integers; verification does not
    # require transcendental evaluation if the enclosures are trusted.
    data={'scale':str(S),'a':a,'threshold':8,'tau':str(tau),'km':km,'kp':kp,
          'ds':[str(d) for d in ds], 'M':[str(M.l),str(M.h)],
          'samples':[[str(v.l),str(v.h)] for v in vals],
          'outward_bracket':[outward(L,False),outward(U,True)]}
    Path(__file__).with_name('zeta_certificate.json').write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
