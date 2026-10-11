#!/usr/bin/env python3
"""Reproduce all local tables and check independent exact identities."""
import sympy as s
from functools import lru_cache
ell,a,t,u=s.symbols('ell a t u')
z2,z3,z4=s.symbols('z2 z3 z4')
g=s.symbols('g')
N=3
C={():1,(1,):0,(2,):z2,(3,):z3,(4,):z4,(1,1):0,(1,1,1):0,(1,1,1,1):0,(2,1):z3,(1,2):-2*z3,(3,1):z4/4,(2,2):3*z4/4,(2,1,1):z4,(1,3):-5*z4/4,(1,2,1):-3*z4,(1,1,2):3*z4}
K={-1:1,0:-s.Rational(1,2),1:s.Rational(1,12),2:0,3:-s.Rational(1,720)}
def integrate(j,P):
    if j==-1:return s.integrate(P,ell)
    return s.expand(sum((-1)**k*s.diff(P,ell,k)/s.Integer(j+1)**(k+1) for k in range(s.degree(P,ell)+1))) if P!=0 else s.Integer(0)
@lru_cache(None)
def word(w):
    if not w:return {0:s.Integer(1)}
    if w[0]>1:
        D={j:-v for j,v in word((w[0]-1,)+w[1:]).items() if j<N}
    else:
        D={}
        for j,v in word(w[1:]).items():
            for k,c in K.items():
                if j+k<N:D[j+k]=D.get(j+k,0)-v*c
    R={0:C[w]}
    for j,v in D.items():
        if v!=0:R[j+1]=s.expand(R.get(j+1,0)+integrate(j,v))
    return R

def comps(p):
    if p==0:yield ()
    for k in range(1,p+1):
        for tail in comps(p-k):yield(k,)+tail

def raw(p):
    R={}
    for w in comps(p):
        mult=s.factorial(p)/s.prod(s.factorial(k) for k in w)
        for j,c in word(w).items():R[j]=s.expand(R.get(j,0)+mult*c)
    return R

def recipgam(m,n):
    log=(g-s.harmonic(m))*u+sum(((-1)**(k+1)*({2:z2,3:z3,4:z4}.get(k,s.zeta(k)))-s.harmonic(m,k))*u**k/k for k in range(2,n+1))
    E=s.series(s.exp(log),u,0,n).removeO()*(-1)**m*s.factorial(m)*u
    return s.expand(E)


# Exact identities are checked in the rational algebra Q[a,g,zeta(2),zeta(3)].
# zeta(4)=2*zeta(2)^2/5 is imposed only after every word is integrated.
import json
from pathlib import Path
checks=[]
def reduced(expr):
    return s.expand(expr).subs(z4,s.Rational(2,5)*z2**2).expand()
def check(name,left,right):
    difference=s.simplify(reduced(left-right))
    if difference!=0:raise AssertionError((name,difference))
    checks.append(name)
L=-ell
Q={1:s.Rational(1,2),2:-1,3:3+z2/2,4:-12-2*z2+3*z3}
T={1:0,2:-s.Rational(1,12),3:s.Rational(1,8),4:-s.Rational(1,4)}
expected={
1:{0:L,1:s.Rational(1,2),2:-s.Rational(1,24),3:0},
2:{0:L**2+z2,1:-1,2:-L/12,3:-s.Rational(1,36)},
3:{0:L**3+3*z2*L-2*z3,1:3+z2/2,2:-L**2/8-L/4-z2/8-s.Rational(3,8),3:s.Rational(5,72)},
4:{0:L**4+6*z2*L**2-8*z3*L+s.Rational(27,2)*z4,1:Q[4],2:-L**3/6-L**2/2-z2*L/2-L-z2/2+z3/3-s.Rational(-0+3,4),3:-z2/18-s.Rational(7,27)}
}
z=s.symbols('z')
U=-sum(s.bernoulli(j,a)*z**j/j for j in range(1,5))
Fparts={}
for p in range(1,5):
    A=raw(p)
    for j in range(4):check(f'local A_{p}, t^{j}',A.get(j,0),expected[p][j])
    for m in range(3):
        E=s.series(s.exp(-a*t)/(1-s.exp(-t)),t,0,m+1).removeO().expand()
        Cm=s.expand(sum(c*E.coeff(t,m-j) for j,c in A.items() if j<=m+1))
        G=recipgam(m,p+1)
        for h in range(1,p+1):
            from_words=sum((-1)**r*s.factorial(r)*Cm.coeff(ell,r)*G.coeff(u,r+1-h) for r in range(h,p+1))
            from_bernoulli=s.factorial(p)/s.factorial(p-h+1)*s.expand((g+U)**(p-h+1)).coeff(z,m+1)
            check(f'principal p={p}, m={m}, h={h}',from_words,from_bernoulli)
        FP=s.expand(sum((-1)**r*s.factorial(r)*Cm.coeff(ell,r)*G.coeff(u,r+1) for r in range(p+1)))
        Fparts[p,m]=reduced(FP)
    b=a-s.Rational(1,2)
    check(f'zero finite part p={p}',Fparts[p,0],Q[p]-b*g**p)
    check(f'minus-one finite part p={p}',Fparts[p,1],g**p/24+T[p]+b*Q[p]+b**2*(p*g**(p-1)-g**p)/2)
    centered2={1:-s.Rational(1,24),2:s.Rational(1,36),3:-s.Rational(1,9)-z2/24,4:s.Rational(13,27)+z2/18-z3/4}[p]
    check(f'centered minus-two value p={p}',Fparts[p,2].subs(a,s.Rational(1,2)),centered2)
    for m in (1,2):
        residue=s.expand((g+U)**p).coeff(z,m)
        check(f'parameter transport p={p}, m={m}',s.diff(Fparts[p,m],a),m*Fparts[p,m-1]-residue)
# Exact pole cancellation is independently checked at several higher indices.
# This finite test accompanies, and does not replace, the all-index parity proof.
Uc=-sum(s.bernoulli(j,s.Rational(1,2))*z**j/j for j in range(1,10))
for p in range(1,7):
    for m in (0,2,4,6,8):
        for h in range(1,p+1):
            residue=s.factorial(p)/s.factorial(p-h+1)*s.expand((g+Uc)**(p-h+1)).coeff(z,m+1)
            check(f'center cancellation p={p}, m={m}, h={h}',residue,0)
result={'status':'PASS','exact_assertion_count':len(checks),'method':'Independent formal multiple-polylog word differentiation and endpoint constants, compared with finite Bernoulli formulas and parameter transport','checks':checks}
output=Path(__file__).resolve().parents[1]/'results'/'harmonic_symbolic_checks.json'
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checks),'exact symbolic identities')
