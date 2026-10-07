"""Exact, optimization-safe checks. No external programs or floating proofs."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent

def require(t,msg):
 if not t: raise ValueError(msg)

def mul(a,b,N):
 c=[Q(0)]*(N+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b[:N-i+1]): c[i+j]+=x*y
 return c

def exact_stirling(N):
 h=[0]*(N+1)
 for d in range(1,N+1):
  for k in range(d,N+1,d):h[k]+=1 if d%2 else -1
 for k in range(1,N+1):
  o=k;v=0
  while o%2==0:o//=2;v+=1
  require(h[k]==(1-v)*sum(o%d==0 for d in range(1,o+1)),'divisor identity')
 row=[1];a=[0]
 fact=[factorial(k) for k in range(N+1)]
 for n in range(1,N+1):
  row=[0]+[(row[k-1] if k else 0)+(n-1)*(row[k] if k<n else 0) for k in range(1,n+1)]
  a.append(sum(row[k]*fact[k-1]*h[k] for k in range(1,n+1)))
 return a

def direct_nested_log(N):
 L=[Q(0)]+[Q(1,j) for j in range(1,N+1)]
 powers=[[Q(1)]+[Q(0)]*N]
 for k in range(1,N+1):powers.append(mul(powers[-1],L,N))
 F=[Q(0)]*(N+1)
 # Direct expansion sum_k (1/k) sum_j (-1)^(j-1)*L^(k*j)/j.
 for k in range(1,N+1):
  # Deliberately independently multiply L^k to make each outer logarithm.
  P=[Q(1)]+[Q(0)]*N
  for j in range(1,N//k+1):
   P=mul(P,powers[k],N)
   c=Q((-1)**(j-1),k*j)
   F=[x+c*y for x,y in zip(F,P)]
 return [F[n]*factorial(n) for n in range(N+1)]

a=exact_stirling(400)
fixture=[]
for line in (ROOT/'b330498.txt').read_text().splitlines():
 if line.strip() and not line.startswith('#'):
  n,x=map(int,line.split());fixture.append((n,x));require(a[n]==x,f'OEIS b-file mismatch n={n}')
require(direct_nested_log(24)==a[:25],'independent formal composition mismatch')
# Exactly certify first-harmonic domination.
eupper=sum((Q(1,factorial(k)) for k in range(10)),Q(0))+Q(1,9*factorial(9))
require(eupper<Q(87,32),'e upper bound')
require(Q(157,50)**2/Q(55,32)>Q(573,100),'exponent lower bound')
require(sum((Q(573,100)**k/factorial(k) for k in range(21)),Q(0))>300,'positive exp Taylor bound')
require(Q(599,89401)<Q(1,100),'first-harmonic tail bound')
result={'status':'PASS','oeis_bfile_terms':len(fixture),'exact_stirling_through':400,'independent_direct_egf_through':24,'divisor_identity_through':400,'first_harmonic_tail_bound':'599/89401 < 1/100','uses_float':False,'assertions_required':False}
print(json.dumps(result,indent=2,sort_keys=True))
