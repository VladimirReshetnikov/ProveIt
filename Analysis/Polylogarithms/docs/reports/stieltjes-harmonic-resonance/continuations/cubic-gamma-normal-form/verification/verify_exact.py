"""Exact regression checks. Python 3; SymPy required. No network access.
The proofs are in article.pdf; finite regression checks do not replace them.
"""
from fractions import Fraction as F
from math import factorial, comb, prod
from pathlib import Path
import json, sys, platform
import sympy as s
from normal_form import trim,add,deriv,functional,reduce,bell_next,coeff
from exploratory_all_orders import formula as exploratory_formula, pol, mul

HERE=Path(__file__).resolve().parent
counts={"normal_decomposition":0,"functional_support":0,"cubic_coefficients":0,
        "quadratic_coefficients":0,"affine_coefficients":0,"generic_density_identities":0,
        "exploratory_higher_order_nonzero_checks":0}

def integral_poly(p):return sum((c/F(j+1) for j,c in enumerate(p) if j%2==0),F(0))
def ipow(p,n):
 q=(F(1),)
 for _ in range(n):q=mul(q,p)
 return q
P2=(F(1),0,F(-2),0,F(1));P3=(F(1),0,F(-3),0,F(3),0,F(-1))
h=(F(1,24),0,F(1,8));kappa=(0,F(1,48),0,F(1,48))

def cubic(a,k,b,n):
 if (k+n)%2:return F(0)
 p=mul(P3,mul(ipow(h,b),ipow(kappa,n-2)))
 moment=integral_poly((F(0),)*k+p)
 W=a+2*k+3*b+4*n
 return -F(factorial(W),9216*factorial(a)*2**k*factorial(k)*factorial(b)*factorial(n))*moment

def quadratic(a,k,b):
 if k%2:return F(0)
 p=mul(P2,ipow(h,b-2));moment=integral_poly((F(0),)*k+p)
 W=a+2*k+3*b
 return F(factorial(W),192*factorial(a)*2**k*factorial(k)*factorial(b))*moment

P={():F(1)};records={};examples=[]
for W in range(31):
 N,H=reduce(P)
 assert add(dict(N),deriv(H))==P
 counts['normal_decomposition']+=1
 for mon in N:
  assert functional(mon)
  counts['functional_support']+=1
 for n in range(2,W//4+1):
  for b in range((W-4*n)//3+1):
   for k in range((W-4*n-3*b)//2+1):
    a=W-4*n-3*b-2*k
    expected=cubic(a,k,b,n);actual=coeff(N,a,k,b,n)
    assert actual==expected,(W,a,k,b,n,actual,expected)
    counts['cubic_coefficients']+=1
    if a==0 and actual:examples.append(dict(weight=W,a=a,k=k,b=b,n=n,coefficient=str(actual)))
 for b in range(2,W//3+1):
  for k in range((W-3*b)//2+1):
   a=W-3*b-2*k;assert coeff(N,a,k,b)==quadratic(a,k,b)
   counts['quadratic_coefficients']+=1
 for k in range(W//2+1):
  a=W-2*k
  expected=F(0) if k%2 else -F(factorial(W),factorial(a)*2**k*factorial(k)*(k-1)*(k+1))
  assert coeff(N,a,k)==expected
  counts['affine_coefficients']+=1
 if W<=24:
  for mon,c in N.items():
   if len(mon)>4:
    assert exploratory_formula(mon)==c
    counts['exploratory_higher_order_nonzero_checks']+=1
 if W in (8,11,14,20,24,30):
  records[W]={"N":{','.join(map(str,m)):str(c) for m,c in N.items()},
              "H":{','.join(map(str,m)):str(c) for m,c in H.items()}}
 P=bell_next(P)

# The four polynomial identities used in the all-index proof.
from density_identities import pure,cubic as cubic_residual,base1,base2
for e in (pure,cubic_residual,base1,base2):
 assert s.cancel(e)==0
 counts['generic_density_identities']+=1

# Independent beta-integral and two-binomial-sum coefficient representations.
for b in range(9):
 for n in range(2,8):
  for k in range(8):
   if (k+n)%2:continue
   W=2*k+3*b+4*n
   total=sum((F(comb(b,j)*3**j*comb(n-2,l),prod(k+n+2*j+2*l-1+2*r for r in range(4)))
              for j in range(b+1) for l in range(n-1)),F(0))
   alt=-F(factorial(W),192*2**k*factorial(k)*factorial(b)*factorial(n)*24**b*48**(n-2))*total
   assert alt==cubic(0,k,b,n)
counts['beta_vs_double_sum']=9*6*4

v=s.symbols('v')
for b in range(8):
 for n in range(2,8):
  p=(1-v*v)**3*(1+3*v*v)**b*(v+v**3)**(n-2)
  for order in range(3):
   for endpoint in (-1,1):assert s.diff(p,v,order).subs(v,endpoint)==0
counts['endpoint_zero_assertions']=8*6*3*2

result={"status":"PASS","scope":"Exact rational and symbolic checks; not proof-assistant certification",
        "exact_checks":{k:v for k,v in counts.items() if not k.startswith("exploratory")},
        "exploratory_checks":{"higher_order_nonzero_coefficients":counts["exploratory_higher_order_nonzero_checks"]},"python":platform.python_version(),"sympy":s.__version__,
        "higher_order_conjecture_status":"unproved; separate exploratory checks only"}
(HERE/'exact_results.json').write_text(json.dumps(result,indent=2)+'\n')
(HERE/'normal_form_certificates.json').write_text(json.dumps(records,indent=2)+'\n')
(HERE/'mixed_coefficient_examples.json').write_text(json.dumps(examples,indent=2)+'\n')
print(json.dumps(result,indent=2))
