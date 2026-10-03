"""Independent exact regular-minor/basis enumeration for rank-two block lifts and degree-three contraction."""
from itertools import combinations
from fractions import Fraction as F
from math import prod
from pathlib import Path
import random,json
rng=random.Random(450592)
def det(A):
 n=len(A)
 if n==0:return 1
 a=[list(row)for row in A];sign=1;previous=1
 for k in range(n-1):
  if a[k][k]==0:
   j=next((j for j in range(k+1,n)if a[j][k]),None)
   if j is None:return 0
   a[k],a[j]=a[j],a[k];sign=-sign
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):a[i][j]=(a[i][j]*pivot-a[i][k]*a[k][j])//previous
  previous=pivot
  for i in range(k+1,n):a[i][k]=0
 return sign*a[-1][-1]
def regular(M,u,v,forced=()):
 n=len(M);c=len(v);out=[F(0)]*(min(n,c)+1);f=set(forced)
 for k in range(min(n,c)+1):
  for J in combinations(range(c),k):
   if not f<=set(J):continue
   vw=prod(v[j]for j in J)
   for I in combinations(range(n),k):
    if det([[M[i][j]for j in J]for i in I]):out[k]+=prod(u[i]for i in I)*vw
 return out
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
lift_checks=0
for q in range(4):
 for case in range(8):
  d=q+2;n=d+rng.randrange(3);c=2+rng.randrange(3)
  C=[[rng.randrange(-2,3)for _ in range(q)]for _ in range(n)]
  D=[[rng.randrange(-2,3)for _ in range(2)]for _ in range(n)]
  while True:
   E=[[rng.randrange(-2,3)for _ in range(c)]for _ in range(2)]
   independent=[(j,k)for j,k in combinations(range(c),2)if E[0][j]*E[1][k]!=E[1][j]*E[0][k]]
   if independent:break
  u=[F(rng.randrange(1,5))for _ in range(n)];v=[F(rng.randrange(1,5))for _ in range(q+c)]
  M=[C[i]+[sum(D[i][a]*E[a][j]for a in range(2))for j in range(c)]for i in range(n)]
  P=regular(M,u,v)
  Q=sum(v[q+j]*v[q+k]for j,k in independent)
  cols=[C[i]+D[i]for i in range(n)]
  cols += [[int(j==k)for k in range(d)]for j in range(q)]
  cols += [[0]*q+[-E[1][j],E[0][j]]for j in range(c)]
  act=u+[1/v[j]for j in range(q)]+[v[q+j]/Q for j in range(c)]
  H=[F(0)]*(d+1)
  for I in combinations(range(len(cols)),d):
   if det([cols[i]for i in I]):H[sum(i<n for i in I)]+=Q*prod(v[:q])*prod(act[i]for i in I)
  assert trim(P)==trim(H),(q,P,H)
  lift_checks+=1
contract_checks=0
for case in range(32):
 n=3+rng.randrange(3);c=2+rng.randrange(4)
 g=[rng.randrange(1,5)for _ in range(3)]
 rows=[[rng.randrange(-3,4)for _ in range(c)]for _ in range(n)]
 M=[[g[i]if i<3 else 0]+rows[i]for i in range(n)]
 u=[F(rng.randrange(1,5))for _ in range(n)];v=[F(rng.randrange(1,5))for _ in range(c+1)]
 P=regular(M,u,v,(0,));U=sum(u[:3])
 virtual=[[g[j]*rows[i][k]-g[i]*rows[j][k]for k in range(c)]for i,j in combinations(range(3),2)]
 virtualweights=[u[i]*u[j]/U for i,j in combinations(range(3),2)]
 H=regular(rows[3:]+virtual,u[3:]+virtualweights,v[1:])
 rhs=[F(0)]+[v[0]*U*x for x in H]
 assert trim(P)==trim(rhs),(M,P,rhs)
 contract_checks+=1
out={'rank_two_block_lifts_checked':lift_checks,'ordinary_column_counts':[0,1,2,3],'degree_three_conditioning_checked':contract_checks,'integer_determinants_and_rational_activities':True,'all_checks_passed':True}
(Path(__file__).resolve().parents[1]/'data'/'matrix_lift_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
