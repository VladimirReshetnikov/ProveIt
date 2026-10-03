from fractions import Fraction as F
from math import comb,factorial
import json,itertools
from pathlib import Path

def add(P,Q,scale=1):
 R=P.copy()
 for t,c in Q.items():
  R[t]=R.get(t,F(0))+scale*c
  if not R[t]:del R[t]
 return R

def mul(P,Q):
 R={}
 for t,c in P.items():
  for s,d in Q.items():
   v=tuple(i+j for i,j in zip(t,s))
   R[v]=R.get(v,F(0))+c*d
 return {t:c for t,c in R.items() if c}

one={(0,0,0,0):F(1)}
x={(1,0,0,0):F(1)};y={(0,1,0,0):F(1)}
a={(0,0,1,0):F(1)};z={(0,0,0,1):F(1)}
n=add(x,one,3);m=add(y,one,2)
def power(P,k):
 R=one
 for _ in range(k):R=mul(R,P)
 return R
def choose(P,k):
 R={t:c/F(factorial(k)) for t,c in one.items()}
 for i in range(k):R=mul(R,add(P,one,-i))
 return R
cert=json.loads(Path(__file__).with_name('rank-five-certificate.json').read_text())
all_A=[]
certificate_rows=[]
hall_rows=[]
for branch in range(2):
 u=mul(n,add(a,z) if branch==0 else a)
 v=mul(m,a if branch==0 else add(a,z))
 A=[]
 for k in range(6):
  P={}
  for p in range(min(3,k)+1):
   for q in range(min(2,k)+1):
    i,j=k-p,k-q
    if not(0<=i<=2 and 0<=j<=3 and p+q<=k):continue
    term=mul(mul(choose(n,p),choose(m,q)),mul(power(u,i),power(v,j)))
    P=add(P,term,comb(2,i)*comb(3,j))
  A.append(P)
 all_A.append(A)
 for k in range(1,5):
  D=add({t:k*(5-k)*c for t,c in mul(A[k],A[k]).items()},mul(A[k-1],A[k+1]),-(k+1)*(6-k))
  row=next(row for row in cert if row['branch']==branch and row['k']==k)
  supplied={tuple(t):F(c) for t,c in row['terms']}
  assert D==supplied,(branch,k,'identity mismatch')
  assert all(c>0 for c in D.values())
  boundary={t[2]:c for t,c in D.items() if t[0]==t[1]==t[3]==0}
  assert boundary and all(c>0 for c in boundary.values())
  certificate_rows.append({'branch':branch,'gap':k,'terms':len(D),'minimum_coefficient':str(min(D.values())),'positive_boundary':{str(k):str(v) for k,v in sorted(boundary.items())}})

def hall(left,right):
 for size in range(1,len(left)+1):
  for T in itertools.combinations(left,size):
   if len({b for b in right if any(c<2 or b<3 for c in T)})<size:return False
 return True
# Three four-block assignments, covering both ratio-order branches and equality.
for nn,mm,uu,vv,ll,rr in [(3,2,F(7),F(2),F(2),F(3)),(3,3,F(2),F(7),F(3),F(2)),(4,2,F(24),F(20),F(3),F(5))]:
 U,V=uu/ll,vv/rr
 branch=0 if U/nn>=V/mm else 1
 aval=min(U/nn,V/mm);zval=abs(U/nn-V/mm)
 values=(nn-3,mm-2,aval,zval)
 expected=[]
 for k,P in enumerate(all_A[branch]):
  normalized=sum(c*values[0]**t[0]*values[1]**t[1]*values[2]**t[2]*values[3]**t[3] for t,c in P.items())
  expected.append(normalized*(ll*rr)**k)
 counts=[F(0)]*6
 for k in range(6):
  for left in itertools.combinations(range(nn+2),k):
   for right in itertools.combinations(range(mm+3),k):
    if hall(left,right):
     i=sum(c<2 for c in left);j=sum(c<3 for c in right)
     counts[k]+=uu**i*vv**j*ll**(k-i)*rr**(k-j)
 assert counts==expected,(nn,mm,counts,expected)
 hall_rows.append({'n':nn,'m':mm,'core_A_activity':str(uu),'core_B_activity':str(vv),'exterior_X_activity':str(ll),'exterior_Y_activity':str(rr),'branch':branch,'a':str(aval),'z':str(zval),'support_coefficients':[str(c) for c in counts]})
print(json.dumps({'status':'PASS','method':'Independent sparse rational reconstruction and Hall-subset support checks','certificate_rows':certificate_rows,'hall_samples':hall_rows,'scope':'Exact finite polynomial certificate for the specified four-block-constant complete-core family only'},indent=2))
