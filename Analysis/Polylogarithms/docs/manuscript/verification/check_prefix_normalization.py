"""Independent rational overlap checks for the all-order determinant proof.

These finite checks diagnose the normalization, column sign and identity
compiler. The manuscript supplies the all-a analytic proof separately.
No delivered code is imported. Requires SymPy, with assertions enabled.
"""
from pathlib import Path
import json,sys
import sympy as s
from sympy.functions.combinatorial.numbers import stirling
V=Path(__file__).resolve().parent
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
y,x=s.symbols('y x');records=[]
def falling(v,k):return s.prod(v-r for r in range(k))
def source(a,b):
 def cell(t,k):
  j=t+k-a+1
  if j<0:return s.S.Zero
  mu=s.bernoulli(2*j)/s.factorial(2*j)
  return mu*(s.factorial(2*b+2*t-2*a+1)/s.factorial(2*b-2*k)+(s.factorial(2*t+1)/s.factorial(2*a-2*k) if k<a else 0))
 return s.Matrix(b,b,cell)
def retained(a,b):
 rows=[]
 for i in range(a):
  n=b-a+i;poly=s.Poly((2*n+2-y)*falling(4*n+2-y,2*i),y)
  d=[sum(poly.nth(j)*stirling(j,h,kind=2) for j in range(h,2*i+2)) for h in range(2*i+2)]
  row=[]
  for ell in range(a):
   N=2*(n-ell)+1;R=2*b-2*a+2+2*ell
   F=falling(2*n,2*ell)*s.prod(2*n+3+r for r in range(2*ell))/s.factorial(2*ell+1)
   correction=sum(d[2*k+1]*falling(N,2*k+1)*2*s.bernoulli(2*b-2*(a-i+ell+k)) for k in range(i+1))
   row.append(2*F+s.factorial(R)*correction/(s.factorial(N)*(2*n+1)*(2*n+2)*s.factorial(2*ell+2)))
  rows.append(row)
 return s.Matrix(rows)
for a,b in [(5,10),(6,12),(7,14),(7,15),(7,16)]:
 M=source(a,b);A=retained(a,b);epsilon=a*(b-a)+a*(a-1)//2
 multiplier=(-1)**epsilon*s.prod(s.factorial(2*b+2*t-2*a+1)/s.factorial(2*b-2*t) for t in range(b))
 multiplier*=s.prod(s.factorial(2*n+1)**2/(s.factorial(4*n+2)*s.factorial(4*n+3)) for n in range(b-a))
 multiplier*=s.prod((2*n+1)*s.factorial(2*n+2)/s.factorial(4*n+2) for n in range(b-a,b))
 original=M.det(method='domain-ge');small=A.det(method='domain-ge');assert original==multiplier*small and original!=0
 assert original!=(-multiplier)*small
 records.append(dict(a=a,b=b,original_dimension=b,retained_dimension=a,exact_multiplier=str(multiplier),retained_determinant=str(small),original_determinant=str(original),passed=True,wrong_sign_rejected=True))
 print('Exact original/retained determinant',a,b,'PASS',flush=True)
# The first new order-fourteen identity has p=14,q=16. Preserve all
# rational inverse rows and finite counterterms, rather than only a rank.
a,b=7,8;M=source(a,b);inverse=M.inv(method='DM');assert M*inverse==inverse*M==s.eye(b)
weights=[]
for k in range(b):
 P=s.Poly(sum(inverse[k,t]*((x+s.Rational(1,2))**(2*b+2*t+1)-(x-s.Rational(1,2))**(2*b+2*t+1)) for t in range(b)),x)
 def tail(order,h):return 1/s.Integer(order-1) if h==0 else s.bernoulli(2*h,s.Rational(1,2))*s.rf(order,2*h-1)/s.factorial(2*h)
 subtraction=s.S.Zero
 for r in range(a+b-1,2*b):
  for h in range(r-a-b+2):
   alpha=sum(tail(2*a,v)*tail(2*b,h-v) for v in range(h+1))
   subtraction+=P.nth(2*r)*alpha*x**(2*(r-a-b+1-h))
 assert all(P.nth(j)==0 for j in range(1,2*P.degree()+1,2))
 weights.append(dict(k=k,even_weight_coefficients=[str(P.nth(2*r)) for r in range(2*b)],subtraction=str(s.expand(subtraction)),target='zeta('+str(2*k)+')'))
out=dict(status='PASS',imports_delivered_code=False,normalization_checks=records,example_tail_orders=[14,16],both_example_inverse_products=True,ordinary_identity_rows=weights,scope='Five exact rational original-versus-retained determinant comparisons and a complete eight-row ordinary-identity compiler. Finite formula diagnostics, separate from the written infinite proof and numerical arithmetic independence.')
(V/'prefix-normalization-exact.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('All exact normalization and order-fourteen identity compiler checks PASS',flush=True)
