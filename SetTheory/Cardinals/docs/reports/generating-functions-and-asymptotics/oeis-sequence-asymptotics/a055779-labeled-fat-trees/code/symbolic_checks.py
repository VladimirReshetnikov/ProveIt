#!/usr/bin/env python3
"""Report203 symbolic identities, adapted from the separately written audit.

This release is an adaptation, not a freshly independent implementation.
Only expected formula data are read; the coefficient producer is not imported.
"""
import sys
sys.dont_write_bytecode = True
import json
from pathlib import Path
import sympy as s

if s.__version__ != '1.14.0':
    raise RuntimeError('Use pinned SymPy 1.14.0 for this reproducibility fixture')

checks = []
def zero(v,label):
    if s.cancel(v) != 0:
        raise RuntimeError('SYMBOLIC CHECK FAILED: '+label)
    checks.append(label)

r,z,M = s.symbols('r z M',positive=True)
F = M*z*s.exp(z)
kap = []
for j in range(9):
    kap.append(s.cancel(F.subs(z,r).subs(M,s.exp(-r)/(r*(1+r)))))
    F = z*s.diff(F,z)
frozen = json.loads((Path(__file__).resolve().parent / 'expected' / 'coefficients.json').read_text())
for j,k in enumerate(frozen['kappas']):
    zero(kap[j]-s.sympify(k,locals={'r':r}),'fixed-M angular cumulant '+str(j))

# Four epsilon orders obtained by formal exponential differential recurrence.
x,eps = s.symbols('x eps')
E = [s.Integer(1)]
for h in range(1,5):
    E.append(s.expand(sum(j*kap[j+2]*x**(j+2)/s.factorial(j+2)*E[h-j]
                          for j in range(1,h+1))/h))
def integrate(poly):
    ans = 0
    for (degree,),c in s.Poly(poly,x).terms():
        if degree%2 == 0:
            ans += c*(-1)**(degree//2)*s.factorial2(degree-1)/kap[2]**(degree//2)
    return s.factor(ans)
s1,s2 = integrate(E[2]),integrate(E[4])
c1 = s.factor(s.Rational(1,12)+s1)
c2 = s.factor(s.Rational(1,288)+s1/12+s2)
d2 = s.factor(c2-c1*c1/2)
for key,value in [('c1',c1),('c2',c2),('d2',d2)]:
    zero(value-s.sympify(frozen[key],locals={'r':r}),key+' expanded rational identity')

# Derive the inverse equations directly, treating L and B as independent constants.
u,L,B = s.symbols('u L B',nonzero=True)
P = s.symbols('P')
ds = s.symbols('d1:5')
ps = [P]
zero(L*(B/L)-B,'displayed p0 residual')
a,c = s.symbols('a c')
zero((B/L).subs(B,2*(L-1-a)-c)-(2-(2*a+2+c)/L),
     'fixed-M bounded p0 identity')
for j in range(1,5):
    trial = s.symbols('p'+str(j))
    h = sum(ps[k]*u**k for k in range(j))+trial*u**j
    expr = L*(h-P)
    expr += sum(s.Rational((-1)**m,(m-1)*m)*h**m*u**(m-1) for m in range(2,j+2))
    expr -= 2*sum(s.Rational((-1)**(m+1),m)*h**m*u**m for m in range(1,j+1))
    expr += sum(ds[m-1]*u**m*sum(s.binomial(-m,k)*(h*u)**k
                    for k in range(j-m+1)) for m in range(1,j+1))
    eq = s.expand(expr).coeff(u,j)
    zero(s.diff(eq,trial)-L,'inverse recursion linear coefficient order '+str(j))
    pj = s.factor(-eq.subs(trial,0)/L)
    zero(eq.subs(trial,pj),'inverse cancellation order '+str(j))
    ps.append(pj)
zero(ps[1]+(P**2/2-2*P+ds[0])/L,'displayed p1')
zero(ps[2]+((P-2)*ps[1]-P**3/6+P**2-ds[0]*P+ds[1])/L,'displayed p2')

# Newton identities for the deficit list, including Poisson expectations.
d,i,lam = s.symbols('d i lam',integer=True,nonnegative=True)
power = [0]+[s.summation(i**k,(i,0,d-1))+d**(k+1) for k in range(1,7)]
es = [s.Integer(1)]
for j in range(1,7):
    es.append(s.factor(sum((-1)**(k-1)*es[j-k]*power[k] for k in range(1,j+1))/j))
    if s.degree(es[j],d)>2*j:
        raise RuntimeError('Incorrect elementary polynomial degree')
    checks.append('elementary polynomial degree '+str(j))
zero(es[1]-(3*d*d-d)/2,'A(d)')
zero(es[2]-(s.Rational(9,8)*d**4-s.Rational(17,12)*d**3+s.Rational(3,8)*d*d-d/12),'e2(d)')
touchard = [s.Integer(1)]
for j in range(1,13):
    touchard.append(s.expand(lam*(touchard[-1]+s.diff(touchard[-1],lam))))
def expectation(poly):
    return s.expand(sum(c*touchard[degree] for (degree,),c in s.Poly(poly,d).terms()))
zero(expectation(es[1])-(3*lam**2+2*lam)/2,'P2 expectation')
zero(expectation(es[1]**2)/2-(9*lam**4+48*lam**3+46*lam**2+4*lam)/8,'P3 expectation')
zero(expectation(es[2])-(s.Rational(9,8)*lam**4+s.Rational(16,3)*lam**3+4*lam**2),'P6 expectation')
for integer_d in range(15):
    actual = [s.Integer(1)]+[s.Integer(0)]*6
    for value in list(range(integer_d))+[integer_d]*integer_d:
        for j in range(6,0,-1):
            actual[j] += value*actual[j-1]
    for j in range(7):
        zero(es[j].subs(d,integer_d)-actual[j],'Newton vs literal factors d='+str(integer_d)+' j='+str(j))

# Reconcile the p parameter, q, C, and the A162695 logarithm amplitude.
p=s.symbols('p',positive=True)
zero((1/kap[2]).subs(r,1/p-1)-p/(1+p-p*p),'2012 p/r prefactor relation')
zero((s.log(1+r)+r*r/(1+r)) + (-r-s.log(r)-s.log(1+r))
     -(1/(1+r)-1-s.log(r)),'q/M parameter identity')

out={'status':'PASS','sympy_version':s.__version__,'checks':checks,
     'check_count':len(checks),'implementation_origin':'adapted prior independent audit','checks_use_assert':False,
     'derived':{'c1':str(c1),'c2':str(c2),'d2':str(d2),
                'p0':'B/L','p1_to_p4':[str(p) for p in ps[1:]],
                'poisson_coefficients_0_to_6':[str((-1)**j*expectation(es[j])) for j in range(7)]}}
print(json.dumps(out,sort_keys=True,indent=2))
