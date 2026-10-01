#!/usr/bin/env python3
"""Exact represented-sector and endpoint-set regression for the middle-gap proof."""
from itertools import combinations
from random import Random
from math import prod
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from endpoint_profiles import endpoints
P=2305843009213693951

# Lucas-Lehmer verifies the exact Mersenne field modulus used below.
ll=4
for _ in range(59):ll=(ll*ll-2)%P
if ll!=0:raise RuntimeError("Mersenne modulus check failed")
rng=Random(937410)
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def cross(a,b):return tuple((a[(i+1)%3]*b[(i+2)%3]-a[(i+2)%3]*b[(i+1)%3])%P for i in range(3))
def det3(a,b,c):return sum(x*y for x,y in zip(cross(a,b),c))%P
def wedge(a,b):return tuple((a[i]*b[j]-a[j]*b[i])%P for i,j in [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)])
def det4(a,b,c,d):
 x=wedge(a,b);y=wedge(c,d)
 return (x[0]*y[5]-x[1]*y[4]+x[2]*y[3]+x[3]*y[2]-x[4]*y[1]+x[5]*y[0])%P
def rank_cols(cols):
 if not cols:return 0
 a=[list(r) for r in zip(*cols)];h=0
 for j in range(len(cols)):
  k=next((i for i in range(h,len(a)) if a[i][j]%P),None)
  if k is None:continue
  a[h],a[k]=a[k],a[h];v=pow(a[h][j],-1,P);a[h]=[x*v%P for x in a[h]]
  for i in range(h+1,len(a)):
   v=a[i][j]
   if v:a[i]=[(x-v*y)%P for x,y in zip(a[i],a[h])]
  h+=1
  if h==len(a):break
 return h
basisE=[tuple(int(i==j) for i in range(4)) for j in range(4)]
counts=dict(configurations=0,sector_identities=0,upper_incidence_checks=0,adjoint_lower_checks=0,auxiliary_Newton_checks=0,middle_gap_checks=0)
least=None
for case in range(120):
 core=[rng.randrange(8) for _ in range(4)]
 if case%10==0:core=[7]*4
 if case%17==0:core=[0]*4
 lm=[1,2,4]+[rng.randrange(1,8) for _ in range(rng.randrange(1,6))]
 rm=[1,2,4,8]+[rng.randrange(1,16) for _ in range(2)]
 w=[rng.randrange(1,5) for _ in rm]
 K=[tuple(rng.randrange(1,100000) if mask>>j&1 else 0 for j in range(3)) for mask in core]
 L=[tuple(rng.randrange(1,100000) if mask>>j&1 else 0 for j in range(3)) for mask in lm]
 R=[tuple(rng.randrange(1,100000) if mask>>j&1 else 0 for j in range(4)) for mask in rm]
 q=sum(bool(det3(*vs)) for vs in combinations(L,3));require(q>0,'exterior left rank')
 normals=[cross(*vs) for vs in combinations(L,2) if any(cross(*vs))]
 VIRT=[tuple(sum(row[j]*v[j] for j in range(3))%P for row in K) for v in normals]
 FL=sum(bool(det3(*vs)) for vs in combinations(normals,3))
 require(4*FL>=3*q*q,('adjoint',case));counts['adjoint_lower_checks']+=1
 def sums(nr,ne,nv):
  s=0
  for J in combinations(range(len(R)),nr):
   wt=prod(w[j] for j in J)
   for EE in combinations(basisE,ne):
    for VV in combinations(VIRT,nv):
     if det4(*([R[j] for j in J]+list(EE)+list(VV))):s+=wt
  return s
 T=sums(4,0,0);A=sums(3,1,0);U=sums(2,2,0);V=sums(1,3,0)
 PP=sums(3,0,1);W=sums(2,1,1);X=sums(1,2,1)
 D=sums(2,0,2);E2=sums(1,1,2);F3=sums(1,0,3)
 require(T>0,'exterior right rank')
 N1=N2=Z=0
 for j,r in enumerate(R):
  Kcols=[tuple(K[i][a] for i in range(4)) for a in range(3)]
  if det4(*Kcols,r):Z+=w[j]
  for ell in L:
   B=[tuple(K[i][a] for i in range(4))+(ell[a],) for a in range(3)]
   for e in basisE:
    if rank_cols(B+[r+(0,),e+(0,)])==5:N1+=w[j]
 for J in combinations(range(len(R)),2):
  wt=prod(w[j] for j in J)
  for ell in L:
   B=[tuple(K[i][a] for i in range(4))+(ell[a],) for a in range(3)]
   if rank_cols(B+[R[j]+(0,) for j in J])==5:N2+=wt
 # Direct graph endpoint sets, with every B selected.
 rows=core+lm;Bcols=[sum(1<<i for i,row in enumerate(rows) if row>>j&1) for j in range(3)]
 C=[]
 for j in range(5):
  C.append(sum(prod(w[i] for i in J)*len(endpoints(tuple(Bcols+[rm[i] for i in J]))) for J in combinations(range(len(R)),j)))
 require([q*V+X+N1+Z,q*U+W+N2,q*A+PP,q*T]==C[1:],('sector mismatch',case,core,lm,rm));counts['sector_identities']+=4
 require(D<=q*N2,('upper incidence',case));counts['upper_incidence_checks']+=1
 require(4*E2>=3*q*N1,('lower E2',case));require(F3==Z*FL,('exact F3',case));require(4*F3>=3*q*q*Z,('lower F3',case))
 require(2*X>=N1,('unit N1',case));require(q*V>=Z,('unit Z',case))
 B2=q*q*U+q*W+D;B1=q**3*V+q*q*X+q*E2+F3
 require(4*B2*B2>=9*B1*C[3],('auxiliary Newton',case));counts['auxiliary_Newton_checks']+=1
 require(8*C[2]*C[2]>=15*C[1]*C[3],('middle gap',case));counts['middle_gap_checks']+=1
 counts['configurations']+=1
out=dict(scope='Exact finite-field and direct endpoint regressions; proof is analytic and unbounded',field_prime=P,**counts,all_pass=True)
(Path(__file__).resolve().parents[1]/'data'/'middle_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
