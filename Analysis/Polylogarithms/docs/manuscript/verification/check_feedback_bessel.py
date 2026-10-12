"""Independent rational checks of the finite Bessel feedback formula.

The comparison solves the original implicit equation by coefficient
iteration. It imports no supplied report code. Finite checks are not the
all-order proof, which follows from two Lagrange inversions.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,comb
import json,sys
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled.')
V=Path(__file__).resolve().parent
def mul(a,b,N):
 c=[Q(0)]*(N+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b[:N+1-i]): c[i+j]+=x*y
 return c
def exponential(a,N):
 b=[Q(1)]+[Q(0)]*N
 for n in range(1,N+1):b[n]=sum(k*a[k]*b[n-k] for k in range(1,n+1))/n
 return b
def original(c,u,N):
 v=[Q(0)]*(N+1)
 for _ in range(N):
  new=[x/(2*u) for x in mul(v,v,N)]
  for m in range(1,N+1):
   e=exponential([m*x for x in v],N-m)
   for j,x in enumerate(e):new[m+j]+=c[m]*x/u
  v=new
 return v
def weight(n,k,u):
 return sum(Q(factorial(k-1+j),factorial(k)*factorial(j)*factorial(k-1-j)*2**j)*Q(n)**(k-1-j)/u**(k+j) for j in range(k))
def proposed(c,u,N):
 result=[Q(0)]*(N+1);p=[Q(1)]+[Q(0)]*N
 for k in range(1,N+1):
  p=mul(p,c,N)
  for n in range(k,N+1):result[n]+=weight(n,k,u)*p[n]
 return result
polylog_cases=general_cases=recurrence_cases=spectral_cases=0
controls={'highest_quadratic_term_required':False,'factor_n_required':False,'recurrence_sign_required':False}
examples={}
for s in [-2,0,1,2,3]:
 N=12;c=[Q(0)]+[Q(n)**(-s) for n in range(1,N+1)]
 for u in [Q(1,2),Q(1),Q(3,2),Q(4)]:
  a=original(c,u,N);b=proposed(c,u,N)
  assert a==b;polylog_cases+=N
  if s==3 and u==4:examples={str(n):str(a[n]) for n in range(1,9)}
for seed in range(4):
 N=10;c=[Q(0)]+[Q((-1)**(m+seed)*(m+seed+1),m+1) for m in range(1,N+1)]
 for u in [Q(-2),Q(1,2),Q(3)]:
  assert original(c,u,N)==proposed(c,u,N);general_cases+=N
for n in range(1,16):
 for u in [Q(1,2),Q(1),Q(4)]:
  for k in range(2,12):
   lhs=k*(k+1)*u*u*weight(n,k+1,u)
   rhs=k*(2*k-1)*weight(n,k,u)+n*n*weight(n,k-1,u)
   assert lhs==rhs;recurrence_cases+=1
   controls['recurrence_sign_required']|=lhs!=k*(2*k-1)*weight(n,k,u)-n*n*weight(n,k-1,u)
# Count ordered compositions by product, independently of convolution.
def composition_products(n,k):
 if k==0:return {1:1} if n==0 else {}
 out={}
 for first in range(1,n-k+2):
  for M,c in composition_products(n-first,k-1).items():out[first*M]=out.get(first*M,0)+c
 return out
support_sizes={}
for n in range(1,11):
 weights={}
 for k in range(1,n+1):
  for M,c in composition_products(n,k).items():weights[M]=weights.get(M,Q(0))+c*weight(n,k,Q(2))
 assert all(w>0 for w in weights.values())
 support_sizes[str(n)]=len(weights)
 # Exact constant-coefficient shift recurrence: roots 1/M.
 characteristic=[Q(1)]
 for M in weights:
  out=[Q(0)]*(len(characteristic)+1)
  for i,x in enumerate(characteristic):out[i]-=x/M;out[i+1]+=x
  characteristic=out
 for s in [-1,0,1,2,3]:
  values=[sum(w*Q(M)**(-s-j) for M,w in weights.items()) for j in range(len(characteristic))]
  assert sum(a*b for a,b in zip(characteristic,values))==0
  c=[Q(0)]+[Q(m)**(-s) for m in range(1,n+1)]
  assert values[0]==original(c,Q(2),n)[n]
  spectral_cases+=1
 nweight=weight(n,n,Q(2))
 assert weights[1]==nweight
 if n>=2:
  controls['highest_quadratic_term_required']|=nweight!=nweight-Q(comb(2*n-2,n-1),n*2**(n-1))*Q(2)**(-(2*n-1))
  controls['factor_n_required']|=weight(n,2,Q(2))!=Q(1,2*2**2)+Q(1,2*2**3)
assert all(controls.values())
result=dict(passed=True,imports_delivered_code=False,polylog_original_equation_coefficients=polylog_cases,general_signed_kernel_coefficients=general_cases,bessel_weight_recurrences=recurrence_cases,exact_spectral_shift_cases=spectral_cases,support_sizes=support_sizes,corruption_controls=controls,example_s3_u4=examples,scope='Exact rational finite checks; universal identities are proved analytically in the manuscript.')
(V/'feedback-bessel-checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
