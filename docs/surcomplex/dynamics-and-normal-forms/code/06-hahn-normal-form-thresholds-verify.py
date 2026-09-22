#!/usr/bin/env python3
"""Exact finite checks for the article. Not a proof of Hahn summability.

Requires Python >= 3.10 and SymPy. No numerical tolerances or external services.
The parameter ring is truncated by TOTAL LABEL DEGREE, not by Hahn valuation.
"""
from __future__ import annotations
import json
from pathlib import Path
from typing import Dict, Tuple
from sympy import QQ, sqrt, Rational
from sympy.polys.rings import ring

K = QQ.algebraic_field(sqrt(2))
P, q1, p1, q2, p2 = ring('q1,p1,q2,p2', K)
xs = (q1,p1,q2,p2)
pairs = ((q1,p1),(q2,p2))
ORDER = 4
Label = Tuple[int,int]
Series = Dict[Label, object]
checks: list[str] = []

def clean(a: Series) -> Series:
    return {k:v for k,v in a.items() if v and sum(k)<=ORDER}

def add(a: Series, b: Series) -> Series:
    c=dict(a)
    for k,v in b.items(): c[k]=c.get(k,P.zero)+v
    return clean(c)

def scale(a: Series, r) -> Series:
    return clean({k:v*r for k,v in a.items()})

def mul(a: Series, b: Series) -> Series:
    c={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            lab=(i+k,j+l)
            if sum(lab)<=ORDER: c[lab]=c.get(lab,P.zero)+v*w
    return clean(c)

def power(a: Series, n: int) -> Series:
    out={(0,0):P.one}
    for _ in range(n): out=mul(out,a)
    return out

def pb(a,b):
    return sum((a.diff(q)*b.diff(p)-a.diff(p)*b.diff(q) for q,p in pairs),P.zero)

def bracket(a: Series,b: Series) -> Series:
    c={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            lab=(i+k,j+l)
            if sum(lab)<=ORDER: c[lab]=c.get(lab,P.zero)+pb(v,w)
    return clean(c)

def exp_ad(chi: Series,a: Series) -> Series:
    out=dict(a); term=dict(a)
    for n in range(1,ORDER+1):
        term=scale(bracket(chi,term),K.one/K.convert(n))
        out=add(out,term)
    return clean(out)

def resonant(poly):
    return P.from_dict({m:c for m,c in poly.items() if m[0]==m[1] and m[2]==m[3]})

def linv(poly):
    out={}
    for mon,c in poly.items():
        k1,k2=mon[0]-mon[1],mon[2]-mon[3]
        if k1==k2==0: raise ValueError('L inverse applied to a resonance')
        out[mon]=c/K.from_sympy(k1+k2*sqrt(2))
    return P.from_dict(out)

def subst(poly, images: tuple[Series,...]) -> Series:
    out={}
    for mon,c in poly.items():
        term={(0,0):P.ground_new(c)}
        for image,n in zip(images,mon): term=mul(term,power(image,n))
        out=add(out,term)
    return out

def subst_series(a: Series,images: tuple[Series,...]) -> Series:
    out={}
    for (i,j),poly in a.items():
        b=subst(poly,images)
        out=add(out,{(i+k,j+l):v for (k,l),v in b.items() if i+j+k+l<=ORDER})
    return out

def zero(a: Series, name: str) -> None:
    if clean(a): raise AssertionError(name+': '+str(a))
    checks.append(name)

def true(value: bool,name: str) -> None:
    if not value: raise AssertionError(name)
    checks.append(name)

I1,I2=q1*p1,q2*p2
A,B=q1**2*p2,p1**2*q2
C=I1*I2
kappa=K.from_sympy(2-sqrt(2))
H={(0,0):I1+P.ground_new(K.from_sympy(sqrt(2)))*I2,(1,0):A+B,(0,1):C}
chi={}
for degree in range(1,ORDER+1):
    current=exp_ad(chi,H)
    for lab,poly in list(current.items()):
        if sum(lab)==degree:
            nr=poly-resonant(poly)
            if nr: chi[lab]=-linv(nr)
N=exp_ad(chi,H)
for lab,poly in N.items(): true(poly==resonant(poly),f'normal form resonant at label {lab}')
for lab,poly in chi.items(): true(not resonant(poly),f'generator gauge at label {lab}')
true(chi[(1,0)]==(B-A)/kappa,'displayed first generator')
true(chi[(1,1)]==(A-B)*(2*I2-I1)/(kappa*kappa),'displayed mixed generator')
true(N[(2,0)]==(I1**2-4*I1*I2)/kappa,'displayed second normal coefficient')
true(N[(0,1)]==I1*I2,'displayed first resonant coefficient')
true((1,1) not in N,'mixed quadratic label has no normal term')

Phi=tuple(exp_ad(chi,{(0,0):z}) for z in xs)
minus=scale(chi,-K.one)
for i in range(4):
    for j in range(4):
        expected={(0,0):pb(xs[i],xs[j])}
        zero(add(bracket(Phi[i],Phi[j]),scale(expected,-K.one)),f'symplectic bracket {i},{j}')
    zero(add(exp_ad(minus,Phi[i]),{(0,0):-xs[i]}),f'inverse Lie map coordinate {i}')
J=(exp_ad(minus,{(0,0):I1}),exp_ad(minus,{(0,0):I2}))
for i in range(2): zero(bracket(H,J[i]),f'first integral {i}')
zero(bracket(J[0],J[1]),'involution of the two actions')
zero(add(subst_series(H,Phi),scale(N,-K.one)),'direct substitution H(Phi)=N')
for i in range(2):
    zero(add(subst_series(J[i],Phi),{(0,0):-(I1,I2)[i]}),f'J_{i}(Phi)=I_{i}')
F=exp_ad(minus,{(0,0):I1**2+I2**3})
zero(bracket(F,H),'nonlinear function of actions is an integral')

for name,series,base in [('chi',chi,2),('normal',N,2)]+[(f'Phi{i}',a,1) for i,a in enumerate(Phi)]:
    for (a,b),poly in series.items():
        true(all(sum(mon)==base+a+2*b for mon in poly),f'degree-defect identity {name} at {(a,b)}')

# Exact boundary example, checked in a rational-function field.
from sympy import symbols, diff, cancel
q,p,e=symbols('q p e')
Q=q/(1-e*q); PP=p*(1-e*q)**2
true(cancel(Q*PP+e*Q**2*PP-q*p)==0,'cubic boundary example Hamiltonian identity')
true(cancel(diff(Q,q)*diff(PP,p)-diff(Q,p)*diff(PP,q)-1)==0,'cubic boundary example symplectic identity')

# Check the simultaneous positivity / failure-of-well-order witness.
weights=[Rational(n)+Rational(1,n) for n in range(2,35)]
shifted=[weights[n-2]-n for n in range(2,35)]
true(all(a<b for a,b in zip(weights,weights[1:])),'original support increasing finite sample')
true(all(a>b>0 for a,b in zip(shifted,shifted[1:])),'rescaled positive support decreasing finite sample')

# Discrete linearization over Q: f(z)=2z+e z^2, f(h(z))=h(2z).
from fractions import Fraction
b={1:Fraction(1)}
for n in range(2,11):
    b[n]=sum(b[j]*b[n-j] for j in range(1,n))/Fraction(2**n-2)
    true((2**n-2)*b[n]==sum(b[j]*b[n-j] for j in range(1,n)),f'discrete recurrence degree {n}')

report={
  'status':'PASS', 'checks':len(checks), 'total_label_degree':ORDER,
  'coefficient_field':'Q(sqrt(2)); auxiliary rational checks',
  'normal_form':{str(k):str(v.as_expr()) for k,v in sorted(N.items())},
  'generator':{str(k):str(v.as_expr()) for k,v in sorted(chi.items())},
  'check_names':checks,
  'limitations':['Finite tests only; no proof of arbitrary Hahn support summability.',
                 'No proof-assistant formalization.',
                 'No floating-point evidence for the Liouville construction is used.']
}
out=Path(__file__).resolve().parents[1]/'data'/'verification.json'
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(f'PASS: {len(checks)} exact checks through total label degree {ORDER}.')
print('Report:',out)
