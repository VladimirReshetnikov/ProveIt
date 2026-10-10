#!/usr/bin/env python3
"""Finite symbolic checks supplementary to the article's analytic proofs."""
from pathlib import Path
import json
import sympy as s

x,y,r,v,T,z,b=s.symbols('x y r v T z b', positive=True)
checks=[]
def check(name, expression):
    answer=s.cancel(s.expand(expression))
    if answer != 0:
        answer=s.simplify(answer)
    assert answer==0,(name,answer)
    checks.append(name)

check('Gaussian kernel derivative',
      s.diff(x*(x+y)/(1+r*r*x*x),x)-(2*x+y-r*r*x*x*y)/(1+r*r*x*x)**2)
check('Rational resolvent decomposition',
      z*z*x*y/((1-z*x)*(1-z*y))
      -z*x*y/(x-y)*(1/(1-z*x)-1/(1-z*y)))
for N in range(1,11):
    d=lambda k:x*y/(x-y)*((1-x*x)**k-(1-y*y)**k)
    E=sum(d(k)/s.Integer(2)**(k+1) for k in range(N))
    g=-x*y*(x+y)/((1+x*x)*(1+y*y))
    R=lambda u:(1-u*u)**N/(1+u*u)
    check(f'exact Euler divided difference N={N}',
          2**N*(E-g)-x*y/(x-y)*(R(y)-R(x)))
for N in range(1,17):
    for n in range(N):
        lhs=sum(2**(N-k-1)*s.binomial(k,n) for k in range(n,N))
        rhs=sum(s.binomial(N,j) for j in range(n+1,N+1))
        check(f'binomial-tail weights N={N} n={n}',lhs-rhs)
for N in range(0,10):
    R=lambda k:(1-x*x)**k/(1+x*x)
    check(f'endpoint I recurrence N={N}',R(N+1)-2*R(N)+(1-x*x)**N)
for N in range(1,10):
    R=lambda k:(1-x*x)**k/((1+x*x)*(1-x))
    check(f'endpoint B recurrence N={N}',R(N+1)-2*R(N)+(1+x)*(1-x*x)**(N-1))
q=s.exp(x)
check('Bose convexity numerator',s.diff(x/(q-1),x,2)-q*((x-2)*q+x+2)/(q-1)**3)
check('convexity auxiliary second derivative',s.diff((x-2)*q+x+2,x,2)-x*q)
primitive=(-s.log(x*x+1)/2+(1+s.sqrt(2))*s.log(x*x-s.sqrt(2)*x+1)/4
           +(1-s.sqrt(2))*s.log(x*x+s.sqrt(2)*x+1)/4+s.atan(x)
           +s.atan(s.sqrt(2)*x-1)/2-s.atan(s.sqrt(2)*x+1)/2)
check('elementary rational half-profile primitive',
      s.diff(primitive,x)-2*(x**3+x**4)/((1+x*x)*(1+x**4)))
coefficients=[]
for k in range(1,7):
    p=s.expand(s.rf(b,k)**2/s.factorial(k))
    coefficients.append({'k':k,'coefficient_without_zeta_and_inverse_gamma':str(p)})
    check(f'density Taylor coefficient k={k}',
          s.diff((1-x)**(-b),x,k).subs(x,0)/s.factorial(k)-s.rf(b,k)/s.factorial(k))
result={'status':'PASS','number_of_exact_checks':len(checks),'checks':checks,
        'large_T_coefficients':coefficients,
        'scope':'Finite algebraic identities only. Analytic convergence, signs and limits are proved in the article.'}
out=Path(__file__).resolve().parents[1]/'data'/'symbolic_checks.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checks),'exact symbolic equalities')
