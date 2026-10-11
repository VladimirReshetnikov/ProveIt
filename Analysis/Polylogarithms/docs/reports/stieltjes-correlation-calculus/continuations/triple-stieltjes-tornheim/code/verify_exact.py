#!/usr/bin/env python3
"""Finite exact checks for Triple Stieltjes--Tornheim calculus.

These tests check algebraic components, not the analytic continuation proof.
Run from any directory. Python >= 3.10 and SymPy are required.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product, permutations
from pathlib import Path
from collections import Counter
import json
import math
import platform
import sympy as S

ROOT = Path(__file__).resolve().parents[1]

@dataclass(frozen=True)
class QI:
    """Exact Gaussian rational; used instead of floating-point complex phases."""
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def coerce(x):
        return x if isinstance(x, QI) else QI(F(x))
    def __add__(self, x):
        x = self.coerce(x); return QI(self.re+x.re, self.im+x.im)
    __radd__ = __add__
    def __neg__(self): return QI(-self.re, -self.im)
    def __sub__(self, x): return self + (-self.coerce(x))
    def __rsub__(self, x): return self.coerce(x) + (-self)
    def __mul__(self, x):
        x=self.coerce(x)
        return QI(self.re*x.re-self.im*x.im, self.re*x.im+self.im*x.re)
    __rmul__=__mul__
    def __truediv__(self, x):
        x=self.coerce(x); d=x.re*x.re+x.im*x.im
        if not d: raise ZeroDivisionError('zero Gaussian rational')
        return self*QI(x.re/d,-x.im/d)
    def __rtruediv__(self, x): return self.coerce(x)/self
    def __pow__(self, n: int):
        if n < 0: return (QI(1)/self)**(-n)
        out=QI(1); base=self
        while n:
            if n&1: out=out*base
            base=base*base; n//=2
        return out

I=QI(0,1)
counts=Counter()

def check(group: str, condition: bool, detail: str='') -> None:
    if not condition: raise AssertionError(f'{group}: {detail}')
    counts[group]+=1

def finite_sector(s, a, N=5):
    def coeff(n, j):
        sign=1 if n>0 else -1
        return I**(-sign*s[j]-n*a[j])*F(1,abs(n)**s[j])
    direct=QI()
    for n1 in range(-N,N+1):
        for n2 in range(-N,N+1):
            n3=-n1-n2
            if n1 and n2 and n3 and abs(n3)<=N:
                direct += coeff(n1,0)*coeff(n2,1)*coeff(n3,2)
    sectors=QI()
    contributions=[]
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        plus=QI(); minus=QI()
        for m in range(1,N):
            for n in range(1,N-m+1):
                den=F(1,m**s[i]*n**s[j]*(m+n)**s[k])
                phase=-s[i]-s[j]+s[k]+m*(a[k]-a[i])+n*(a[k]-a[j])
                plus += I**phase*den
                minus += I**(-phase)*den
        contributions.append((plus,minus)); sectors+=plus+minus
    return direct,sectors,contributions

for a in [(0,1,2),(0,1,3)]:
    for s in product(range(4),repeat=3):
        direct,sectors,_=finite_sector(s,a)
        check('six_sector_finite_fourier',direct==sectors,f'{s} {a}')
canary=False
for s in product(range(4),repeat=3):
    direct,sectors,terms=finite_sector(s,(0,1,3))
    if terms[0][0]!=QI():
        canary=(direct != sectors-2*terms[0][0]); break
check('corruption_controls',canary,'reverse one sector sign')

points=[QI(1),QI(-1),I,-I,QI(F(3,5),F(4,5))]
def T000(z,w): return z/(1-z)*w/(1-w)
for a in permutations(points,3):
    total=QI()
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        z=a[k]/a[i]; w=a[k]/a[j]
        total += T000(z,w)+T000(1/z,1/w)
    check('zero_order_kernel_equals_two',total==QI(2))

x,y,u=S.symbols('x y u')
for r in range(1,9):
    for s in range(1,9):
        rhs=0
        for j in range(1,r+1):
            rhs+=S.binomial(r+s-j-1,s-1)*x**(r-j)*y**s*(x+y)**(j-1)
        for j in range(1,s+1):
            rhs+=S.binomial(r+s-j-1,r-1)*x**r*y**(s-j)*(x+y)**(j-1)
        check('integer_tornheim_partial_fraction',S.expand((x+y)**(r+s-1)-rhs)==0,f'{r} {s}')

cot_cases=[]
for depth in range(1,11):
    poles=list(S.primerange(2,40))[:depth]
    co=[S.prod(S.I*(a+b)/(a-b) for b in poles if a!=b) for a in poles]
    c0=S.cos(S.pi*depth/2)
    den=S.prod(x-a for a in poles)
    residual=S.I**depth*S.prod(x+a for a in poles)-c0*den
    for a,c in zip(poles,co):
        residual -= c*S.I*(x+a)*S.prod(x-b for b in poles if a!=b)
    check('all_depth_cotangent_partial_fraction',S.expand(residual)==0,str(depth))
    check('cotangent_residue_sum',S.simplify(sum(co)-S.sin(S.pi*depth/2))==0,str(depth))
    cot_cases.append({'depth':depth,'poles':poles,'constant':str(c0),'coefficients':[str(c) for c in co]})
check('corruption_controls',S.cos(S.pi*2/2)!=0,'dropping even-depth constant')

MAX=12
a=S.symbols('a0:'+str(MAX+2)); b=S.symbols('b0:'+str(MAX+2))
za=-1/u+sum(a[j]*u**j/S.factorial(j) for j in range(MAX+2))
zb=-1/u+sum(b[j]*u**j/S.factorial(j) for j in range(MAX+2))
csc=S.series(S.pi/S.sin(S.pi*u),u,0,MAX+3).removeO()
cot=S.series(S.pi*S.cot(S.pi*u),u,0,MAX+3).removeO()
raw=S.expand(csc*zb-cot*za+(a[0]-b[0])/u)
I_table=[]
for m in range(MAX+1):
    closed=(b[m+1]-a[m+1])/S.Integer(m+1)
    for k in range(1,(m+1)//2+1):
        j=m-2*k+1
        closed += 2*S.factorial(m)*S.zeta(2*k)/S.factorial(j)*((1-S.Integer(2)**(1-2*k))*b[j]+a[j])
    if m%2==0:
        closed -= 2*S.factorial(m)*(2-S.Integer(2)**(-m-1))*S.zeta(m+2)
    actual=S.factorial(m)*raw.coeff(u,m)
    check('stieltjes_cotangent_coefficients',S.expand(actual-closed)==0,str(m))
    I_table.append({'m':m,'expression':str(S.expand(closed)),'latex':S.latex(S.expand(closed))})
check('corruption_controls',S.expand(S.factorial(0)*raw.coeff(u,0)-(b[1]-a[1]))==-S.pi**2/2,'missing quadratic constant')

def hs(N,J):
    """Complete homogeneous harmonics using Newton's power-sum recurrence."""
    out=[S.Integer(1)]
    for j in range(1,J+1):
        out.append(S.factor(sum(S.harmonic(N,k)*out[j-k] for k in range(1,j+1))/j))
    return out

def hs_direct(N,J):
    out=[S.Integer(1)]+[S.Integer(0)]*J
    for k in range(1,N+1):
        old=out[:]
        out=[sum(old[j-l]/S.Integer(k)**l for l in range(j+1)) for j in range(J+1)]
    return out

for N in range(0,13):
    h=hs(N,10); h2=hs_direct(N,10)
    for j in range(11):check('complete_harmonic_coefficients',h[j]==h2[j],f'{N} {j}')
    pol=S.Poly(S.prod(1+u/S.Integer(k) for k in range(1,N+1)),u)
    e=[S.Integer(1)]
    for j in range(1,N+1):
        e.append(S.factor(sum((-1)**(k-1)*S.harmonic(N,k)*e[j-k] for k in range(1,j+1))/j))
    for j in range(N+1): check('elementary_harmonic_coefficients',e[j]==pol.nth(j),f'{N} {j}')

for r in range(2,13):
    for m in range(9):
        h=hs(r-1,m+1); hp=hs(r-2,m+1)
        A=[(-1)**(m+1)*S.factorial(m)/S.factorial(r-1)*h[m+1-j]/S.factorial(j) for j in range(m+2)]
        B=[(-1)**(m+1)*S.factorial(m)/S.factorial(r-2)*hp[m+1-j]/S.factorial(j) for j in range(m+2)]
        derivative=[(r-1)*A[j]-(j+1)*A[j+1] if j<m+1 else (r-1)*A[j] for j in range(m+2)]
        check('primitive_derivative_ladder',derivative==B,f'{r} {m}')

summary={'schema':'triple-stieltjes-exact-v1','python':platform.python_version(),'sympy':S.__version__,
         'status':'PASS','counts':dict(counts),'total_assertions':sum(counts.values()),
         'scope':'Finite algebra only. Analytic theorems are proved in article.tex; not proof-assistant formalization.'}
(ROOT/'results').mkdir(exist_ok=True)
(ROOT/'results'/'exact_checks.json').write_text(json.dumps(summary,indent=2)+'\n')
(ROOT/'results'/'stieltjes_cotangent_coefficients.json').write_text(json.dumps(I_table,indent=2)+'\n')
(ROOT/'results'/'cotangent_partial_fractions.json').write_text(json.dumps(cot_cases,indent=2)+'\n')
print(json.dumps(summary,indent=2))
