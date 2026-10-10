#!/usr/bin/env python3
"""Finite symbolic audits of formulas; these are not analytic proof checks."""
from pathlib import Path
import json
import sympy as s

x,y,r,z,u = s.symbols('x y r z u', real=True)
b,v = s.symbols('b v', positive=True)
checks = {}
def check(name, lhs, rhs=0):
    residue = s.simplify(s.together(s.expand_complex(lhs-rhs))) if (lhs-rhs).has(s.I) else s.simplify(s.together(lhs-rhs))
    assert residue == 0, (name,residue)
    checks[name] = 'exact zero'

H=x*(x+y)/((1+r*r*x*x)*(1+r*r*y*y))
check('Gaussian kernel derivative',s.diff(H,x),
      (2*x+y-r*r*x*x*y)/((1+r*r*y*y)*(1+r*r*x*x)**2))
check('Real kernel derivative',s.diff(x/((1-z*x)*(1-z*y)),x),
      1/((1-z*y)*(1-z*x)**2))
check('Gaussian imaginary part',s.im((s.I*r)**2/((1-s.I*r*x)*(1-s.I*r*y))),
      -r**3*(x+y)/((1+r*r*x*x)*(1+r*r*y*y)))
check('Centered Stieltjes factor',z/(1-z)-z/(1-z*u),
      z*z*(1-u)/((1-z)*(1-z*u)))
# Algebraic normalization of the power-balance antiderivative derivative.
a=s.symbols('a',positive=True)
derivative = s.diff(-((1-v)**a-1)*v**(-a)/a,v)
target=((1-v)**(a-1)-1)*v**(-a-1)
res=s.simplify((derivative-target)*v**(a+1))
common=s.symbols('common_power')
res=res.xreplace({(1-v)**a:(1-v)*common, (1-v)**(a-1):common})
assert s.simplify(res)==0
checks['Power-balance antiderivative']='exact zero after positive-base power rule'
# Critical Euler endpoint recurrences, valid independently of integral evaluation.
N=s.symbols('N',integer=True,positive=True)
q=s.symbols('q')
check('Euler kernel one-step recurrence',(1-u*u)*q,2*q-(1+u*u)*q)
check('Left endpoint integrand cancellation',(1-u*u)/(1-u),1+u)
# Laurent coefficient: zeta(1+b) and reciprocal gamma(1-b).
g, g1, z2 = s.symbols('gamma gamma1 zeta2')
za=1/b+g-g1*b
rg=1-g*b+(g*g-z2)*b*b/2
coef=s.series(b*b*za*rg,b,0,4).removeO()
check('A(b) has no quadratic term',coef,b-(g1+(g*g+z2)/2)*b**3)
# Euler finite-weight identity over an exhaustive finite test grid.
count=0
for n in range(1,33):
    for j in range(n):
        left=sum(2**(n-k-1)*s.binomial(k,j) for k in range(j,n))
        right=sum(s.binomial(n,k) for k in range(j+1,n+1))
        assert left==right
        count+=1
out={'status':'PASS','sympy_version':s.__version__,
     'symbolic_identities':checks,'finite_binomial_weight_checks':count,
     'limits':'Convergence, domination, positivity on full domains, and asymptotic uniformity are proved in the article, not by these finite tests.'}
p=Path(__file__).resolve().parents[1]/'data'/'symbolic_checks.json'
p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS:',len(checks),'symbolic identities;',count,'finite binomial checks')
