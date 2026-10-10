#!/usr/bin/env python3
"""Independent symbolic replay: derives rational kernels instead of importing them."""
from __future__ import annotations
from math import comb
from itertools import product
import sympy as s
p,y,t,lam=s.symbols('p y t lam')

def require(ok,msg):
    if not ok:raise ValueError(msg)

def bern(poly,variables,degrees):
    P=s.Poly(poly,*variables);result=[]
    for ii in product(*(range(d+1) for d in degrees)):
        total=s.S(0)
        for kk,c in P.terms():
            if all(k<=i for k,i in zip(kk,ii)):
                z=c
                for k,i,d in zip(kk,ii,degrees):z*=s.Rational(comb(i,k),comb(d,k))
                total+=z
        result.append(total)
    return result

for n,d in [(2,8),(3,4)]:
    kernel=s.cancel(((1-p*y*y)**n/(1+p*y*y)-(1-p)**n/(1+p))/(1-y))
    polynomial=s.cancel((s.Rational(9,8)-kernel)*8*(1+p)*(1+p*y*y))
    deg=(s.degree(polynomial,p),s.degree(polynomial,y));mins=[]
    for i,j in product(range(d),repeat=2):
        q=s.Poly(polynomial.subs({p:(p+i)/d,y:(y+j)/d}),p,y).as_expr()
        values=bern(q,(p,y),deg);require(min(values)>0,'kernel certificate failed')
        mins.append(min(values))
    print(f'PASS: directly derived N={n} kernel, global Bernstein minimum {min(mins)}')
q=s.cancel((9*(1-t**8)**3-8*(1+t**3)*(1-t**6)**3)/(1-t*t)**3)
mins=[]
for i in range(2):
    bb=bern(s.expand(q.subs(t,(t+i)/2)),(t,),(18,));require(min(bb)>0,'J4 failed');mins.append(min(bb))
print('PASS: J4 envelope, interval minima',mins)
# Independent generating-function and recurrence comparison through degree 12.
series=s.series((1+t)**((lam-1)/2)*(1-t)**(-(lam+1)/2),t,0,13).removeO().expand()
P=[s.S(1),lam]
for n in range(1,12):P.append(s.expand((lam*P[n]+n*P[n-1])/(n+1)))
for n in range(13):require(s.simplify(series.coeff(t,n)-P[n])==0,'moment polynomial failed')
print('PASS: 13 moment-polynomial generating coefficients')
# Recover the three explicit elementary error sums from F_11 and its derivatives.
z=s.symbols('z');f=s.log(1-z)**2/2;D=lambda h:s.simplify(z*s.diff(h,z))
g=[]
for j in range(5):
    g.append(s.simplify(s.im(s.expand_complex(f.subs(z,s.I)))))
    f=D(f)
actual=[s.simplify(-g[1]),s.simplify(-(g[2]+g[0])/2),s.simplify(-(g[3]+5*g[1])/6)]
expected=[s.pi/8+s.log(2)/4,
          s.Rational(1,4)+s.pi*(1+s.log(2))/16,
          s.Rational(1,8)+s.log(2)/6+5*s.pi/48]
for lhs,rhs in zip(actual,expected):
    require(s.simplify(lhs-rhs)==0,'explicit elementary identity failed')
require(s.simplify(g[4]-(1+s.pi/4))==0,'negative-order sign example failed')
print('PASS: three explicit elementary identities and g_{-3,1}=1+pi/4')
print('First three moment sums:',*actual)
print('ALL INDEPENDENT SYMBOLIC CHECKS PASSED')
