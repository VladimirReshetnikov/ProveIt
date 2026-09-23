#!/usr/bin/env python3
"""Exact finite checks for the accompanying article; not a formal proof checker."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

checks: list[dict[str, object]] = []
def equal(name: str, lhs: s.Expr, rhs: s.Expr) -> None:
    difference = s.factor(s.cancel(lhs-rhs))
    if difference != 0:
        raise AssertionError(f'{name}: {difference}')
    checks.append({'name': name, 'passed': True})
def truth(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    checks.append({'name': name, 'passed': True})
def mul(a, b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    return s.Matrix([a0*b0-a1*b1-a2*b2-a3*b3,
                     a0*b1+a1*b0+a2*b3-a3*b2,
                     a0*b2-a1*b3+a2*b0+a3*b1,
                     a0*b3+a1*b2-a2*b1+a3*b0])
def chi(q):
    a,b,c,d=q
    return s.Matrix([[a+s.I*b,c+s.I*d],[-c+s.I*d,a-s.I*b]])

u=s.Matrix(s.symbols('u1:4', real=True)); v=s.Matrix(s.symbols('v1:4',real=True))
a=s.Matrix([1,*u]); b=s.Matrix([1,*v]); ac=s.Matrix([1,*(-u)]); bc=s.Matrix([1,*(-v)])
Da=1+u.dot(u); Db=1+v.dot(v); D=s.expand(Da*Db)
num=mul(mul(mul(a,b),ac),bc).applyfunc(s.expand)
X=u.cross(v); XX=s.expand(X.dot(X))
equal('generic commutator scalar numerator',num[0],D-2*XX)
equal('generic commutator unit norm',s.expand(num.dot(num)),D**2)
cm1=num-s.Matrix([D,0,0,0])
equal('generic commutator distance squared',s.expand(cm1.dot(cm1)),4*XX*D)
for k,z in enumerate(mul(a,b)-mul(b,a)-s.Matrix([0,*(2*X)])):
    equal(f'quaternion commutator vector {k}',z,0)
for k,z in enumerate(chi(mul(a,b))-chi(a)*chi(b)):
    equal(f'complex representation multiplicativity {k}',z,0)

x=s.symbols('x',real=True)
for m in range(1,17):
    T=s.chebyshevt(m,x); Q=s.chebyshevu(m-1,x)
    equal(f'Chebyshev norm identity m={m}',T*T+(1-x*x)*Q*Q,1)
    equal(f'Chebyshev first derivative m={m}',s.diff(T,x).subs(x,1),m*m)
    equal(f'Chebyshev second derivative m={m}',s.diff(T,x,2).subs(x,1),s.Rational(m*m*(m*m-1),3))

w,p=s.symbols('w p',positive=True)
c=1-w; d=1-w/p
k0sq=p*(1+d)/(1+c); k1sq=p*(1-d)/(1-c)
equal('filter second diagonal squared',k1sq,1)
equal('filter first diagonal squared',k0sq,(2*p-w)/(2-w))
equal('filter success probability',k0sq*(1+c)/2+k1sq*(1-c)/2,p)
equal('filter successful overlap',k0sq*(1+c)/2-k1sq*(1-c)/2,p*d)
equal('postselection exact distance squared',1-d*d,2*w/p-(w/p)**2)
for wn in [s.Rational(1,1000),s.Rational(1,100),s.Rational(1,10),s.Rational(1,3)]:
    for pn in [wn/3,wn,2*wn,(1+wn)/2,s.Integer(1)]:
        dn=max(s.Integer(0),1-wn/pn)
        aa=pn*(1+dn)/(2-wn); bb=pn*(1-dn)/wn
        truth(f'filter contraction w={wn} p={pn}',bool(0<=aa<=1 and 0<=bb<=1))
        equal(f'filter normalization w={wn} p={pn}',aa*(2-wn)/2+bb*wn/2,pn)
        equal(f'filter overlap w={wn} p={pn}',aa*(2-wn)/2-bb*wn/2,pn*dn)

h=s.symbols('h',positive=True)
u1=s.Matrix([h,0,0]); v1=s.Matrix([h,h**3,0])
w1=2*u1.cross(v1).dot(u1.cross(v1))/((1+u1.dot(u1))*(1+v1.dot(v1)))
equal('nearly aligned example exact Wilson defect',w1,2*h**8/((1+h*h)*(1+h*h+h**6)))
equal('nearly aligned example leading coefficient',s.limit(w1/h**8,h,0),2)
for m in range(1,9):
    wm=1-s.chebyshevt(m,1-w1)
    equal(f'example query leading coefficient m={m}',s.limit(wm/h**8,h,0),2*m*m)
# Equality examples for the conditioning estimate, all diagonal (classical) states.
for pn in [s.Rational(1,100),s.Rational(1,5),s.Rational(1,2)]:
    for dn in [pn/10,pn/2,pn]:
        rho=[1-pn,pn,0]; sig=[1-pn,pn-dn,dn]
        din=sum(abs(a-b) for a,b in zip(rho,sig))/2
        dout=(abs(1-(pn-dn)/pn)+abs(dn/pn))/2
        equal(f'conditioning sharpness p={pn} delta={dn}',dout,din/pn)

n,m=s.symbols('n m',integer=True,positive=True)
equal('quaternionic composite dimension obstruction',(2*n*n-n)*(2*m*m-m)-(2*n*n*m*m-n*m),2*n*m*(n-1)*(m-1))
# A symbolic quaternionic pure state and an effect: check trace normalization.
q=s.Matrix([s.Rational(1,2),s.Rational(1,2),s.Rational(1,2),s.Rational(1,2)])
M=chi(q)
for k,z in enumerate(M.conjugate().T*M-s.eye(2)):
    equal(f'surquaternion simulation unitary entry {k}',z,0)

report={'status':'all exact checks passed','count':len(checks),'sympy_version':s.__version__,
        'scope':'Finite polynomial, rational and formal-leading-coefficient identities only. '
                'No formal verification of general theorems, surreal fields, adaptive optimality, '
                'or physical realizability is claimed.', 'checks':checks}
root=Path(__file__).resolve().parent
(root/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'verification.txt').write_text(f"{len(checks)} exact checks passed. SymPy {s.__version__}.\n"+report['scope']+'\n')
print((root/'verification.txt').read_text(),end='')
