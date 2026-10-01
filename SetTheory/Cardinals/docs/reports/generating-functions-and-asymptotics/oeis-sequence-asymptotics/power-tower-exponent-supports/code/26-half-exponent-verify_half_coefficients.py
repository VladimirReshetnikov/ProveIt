"""Exact half-exponent coefficient and diagonal checks.

Finite computations support the separate analytic proofs; no inference of a
full zero classification is made. Python standard library only.
"""
from fractions import Fraction as F
from math import comb,factorial
from collections import defaultdict
from pathlib import Path
import json,hashlib
LIMIT=36

def mul(a,b):
 out=[F(0)]*min(LIMIT+1,len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b[:len(out)-i]):
    if y:out[i+j]+=x*y
 return out

def binom(a,n):
 v=F(1)
 for j in range(n):v*=F(a-j,j+1)
 return v

def powers(a,n):
 out=[[F(1)]]
 for _ in range(n):out.append(mul(out[-1],a))
 return out

logs=powers([F(0)]+[F((-1)**(j+1),j) for j in range(1,LIMIT+1)],5)
ats=powers([F(0)]+[F(1,j) if j%2 else F(0) for j in range(1,LIMIT+1)],5)
sqs=powers([F(0)]+[binom(F(1,2),j) for j in range(1,LIMIT+1)],5)
count=zeros=0;digest=hashlib.sha256()
for k in range(6):
 for d in range(6):
  if k+d==0:continue
  left=mul(mul(sqs[k],[binom(F(d,2),j) for j in range(LIMIT+1)]),logs[d])
  base=mul(ats[d],[F(comb(d+1,j)) for j in range(d+2)])
  for N in range(max(1,k+d),min(LIMIT,k+d+12)+1):
   e=2*N-k-d-1
   right=mul(base,[F(comb(e,j)*(-1)**j) for j in range(e+1)])
   lhs=left[N] if N<len(left) else F(0)
   rhs=(right[N-k] if N-k<len(right) else F(0))*2**k*F(4)**(d-N)
   if lhs!=rhs:raise RuntimeError(('identity',N,k,d,lhs,rhs))
   count+=1;zeros+=lhs==0;digest.update(f'{N},{k},{d}:{lhs}\n'.encode())

p={(0,0):1};diagonal_checks=0;extra=[];counts=[]
for N in range(1,151):
 out=defaultdict(int)
 for (ell,k),v in p.items():
  out[ell,k]+=(ell-2*(N-1))*v
  if k:out[ell,k-1]+=2*k*v
  out[ell+1,k]+=2*v;out[ell+1,k+1]+=v
 p={key:v for key,v in out.items() if v}
 for r in (1,2,3):
  ell=N-r
  if ell<1:continue
  for k in range(ell+1):
   actual=F(p.get((ell,k),0),2**N)
   if r==1:
    predicted= -F(comb(N,2),4)*F(comb(N-2,k-1),2**(k-1)) if k else F(0)
   elif r==2:
    predicted=F(N*(N-1)*comb(N-2,k)*(3*k*k+13*k-4*N+8),96*2**k)
   else:
    predicted=-F(N*(N-1)*(N-2)*comb(N-3,k)*(k+4)*(k*k+9*k-4*N+12),384*2**k)
   if actual!=predicted:raise RuntimeError(('diagonal',N,r,k,actual,predicted))
   diagonal_checks+=1
 for ell in range(1,N+1):
  for k in range(ell+1):
   if (ell,k) not in p:
    reflected=(ell==N-1 and k==0)
    if not reflected:extra.append([N,ell,k])
 if N<=12 or N in (50,100,150):counts.append([N,len(p)])
expected=[]
for k in range(1,151):
 if k%4 in (0,1):
  N=(3*k*k+13*k+8)//4
  if N<=150:expected.append([N,N-2,k])
 if k>=3 and k%4 in (0,3):
  N=(k*k+9*k+12)//4
  if N<=150:expected.append([N,N-3,k])
if sorted(extra)!=sorted(expected):raise RuntimeError(('additional finite zeros',extra,expected))
result={'exact_transform_identities':count,'included_zero_cases':zeros,
        'transform_digest':digest.hexdigest(),'diagonal_coefficient_checks':diagonal_checks,
        'scanned_max_order':150,'nonreflection_zeros':extra,'term_counts':counts,
        'scope':'finite exact regression only; no global zero classification'}
Path(__file__).with_name('half_coefficient_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:val for key,val in result.items() if key!='nonreflection_zeros'},indent=2))
