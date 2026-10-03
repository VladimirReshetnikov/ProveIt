"""Exact finite checks of generalized derivative coefficient identities.

Only Python's standard library is required. The analytic density theorem does
not depend on these finite regressions.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib,json
LIMIT=110

def mul(a,b):
 out=[F(0)]*min(LIMIT+1,len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b[:len(out)-i]):
    if y:out[i+j]+=x*y
 return out

def powers(a,n):
 out=[[F(1)]]
 for _ in range(n):out.append(mul(out[-1],a))
 return out

lp=powers([F(0)]+[F((-1)**(j+1),j) for j in range(1,LIMIT+1)],3)
ap=powers([F(0)]+[F(1,j) if j%2 else F(0) for j in range(1,LIMIT+1)],3)
count=zeros=bulk=0;digest=hashlib.sha256();depth_checks=0
for a in range(1,9):
 B=[F(comb(a,j+1)) for j in range(a)]
 C=[F(comb(a,j+1),a) if j%2==0 else F(0) for j in range(a)]
 bp=powers(B,3);cp=powers(C,3)
 for k in range(4):
  for d in range(4):
   plus=[F(comb(a*d,j)) for j in range(a*d+1)]
   left=mul(mul(bp[k],plus),lp[d])
   bare=mul(mul(cp[k],plus),ap[d])
   for q in sorted(set([-a*d-1,-1,0,1,a*d,a*d+1])):
    N=a*(k+d)+q+1;M=N-k
    if M<d or N<0 or M>LIMIT:continue
    minus=([F(comb(-q+j-1,j)) for j in range(LIMIT+1)] if q<0 else
           [F(comb(q,j)*(-1)**j) for j in range(q+1)])
    right=mul(bare,minus)
    lhs=left[M] if M<len(left) else F(0)
    rhs=(right[M] if M<len(right) else F(0))*a**k*F(2)**(-(a-1)*(k+d)-q-1)
    if lhs!=rhs:raise RuntimeError(('identity',a,k,d,q,lhs,rhs))
    H=lhs*F(factorial(M),factorial(d))
    if H.denominator!=1:raise RuntimeError(('integrality',a,k,d,q,H))
    if q<0:
     if H<=0:raise RuntimeError(('bulk',a,k,d,q,H))
     bulk+=1
    if d in (1,2) and q>=0:
     parity=((a-1)*k+d)%2
     expected=(-1)**q if parity else (-1)**q*((a*d>q)-(a*d<q))
     if (H>0)-(H<0)!=expected:raise RuntimeError(('depth sign',a,k,d,q,H,expected))
     depth_checks+=1
    count+=1;zeros+=H==0;digest.update(f'{a},{k},{d},{q}:{H}\n'.encode())
result={'exact_identities':count,'included_zero_cases':zeros,'positive_bulk_checks':bulk,
        'depth_one_two_sign_checks':depth_checks,'exponents':list(range(1,9)),
        'sha256':digest.hexdigest(),'scope':'finite exact regression only'}
Path(__file__).with_name('general_coefficient_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
