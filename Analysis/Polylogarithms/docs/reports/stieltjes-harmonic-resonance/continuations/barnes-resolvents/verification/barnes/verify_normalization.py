"""Exact coefficient checks of the all-rank multiple Gamma normalization."""
from pathlib import Path
import json
import sympy as s

x,n,X=s.symbols('x n X')
z=s.symbols('zeta_derivative_0:7')
checks={}

def check(name,expr):
    residual=s.cancel(s.expand(expr))
    assert residual == 0, (name,residual)
    checks[name]=True

def coefficient(r,k):
    return s.Poly(s.prod(X+h-x for h in range(1,r)),X).coeff_monomial(X**k)/s.factorial(r-1)

def L_at_one(r):
    return sum(coefficient(r,k).subs(x,1)*z[k] for k in range(r))

def binom_poly(v,j):
    return s.prod(v-h for h in range(j))/s.factorial(j)

def Q(r):
    return sum((-1)**(j+1)*L_at_one(r-j)*binom_poly(x-1,j) for j in range(r))

for r in range(1,7):
    reconstructed=sum(coefficient(r,k)*(n+x)**k for k in range(r))
    check('multiplicity_polynomial_rank_'+str(r),
          reconstructed-s.prod(n+h for h in range(1,r))/s.factorial(r-1))
    check('normalization_at_one_rank_'+str(r), Q(r).subs(x,1)+L_at_one(r))
    if r>=2:
        check('normalization_recurrence_rank_'+str(r),Q(r).subs(x,x+1)-Q(r)+Q(r-1))

a,b=s.symbols('a b')
check('corrected_pointwise_reflection_algebra',
      (a*a+b*b)/2-((a+b)**2+(a-b)**2)/4)
report=dict(exact_checks=len(checks),all_passed=all(checks.values()),
            sympy_version=s.__version__,checks=checks,
            interpretation='Finite symbolic diagnostics complement the general proofs.')
Path(__file__).with_name('normalization_exact.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
