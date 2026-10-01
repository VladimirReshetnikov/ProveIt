#!/usr/bin/env python3
"""Independent endpoint/represented-sector regression; no population bound enters proofs."""
from itertools import combinations
from random import Random
from math import prod
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from endpoint_profiles import endpoints
P=2305843009213693951
ll=4
for _ in range(59):ll=(ll*ll-2)%P
if ll:raise RuntimeError('field primality check')
rng=Random(5382026)
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def rank(cols):
 if not cols:return 0
 rows=[list(r) for r in zip(*cols)];h=0
 for j in range(len(cols)):
  k=next((i for i in range(h,len(rows)) if rows[i][j]%P),None)
  if k is None:continue
  rows[h],rows[k]=rows[k],rows[h];piv=rows[h][j]%P
  for i in range(h+1,len(rows)):
   v=rows[i][j]%P
   if v:
    rows[i]=[(piv*x-v*y)%P for x,y in zip(rows[i],rows[h])]
  h+=1
  if h==len(rows):break
 return h

def cross(a,b):return tuple((a[(i+1)%3]*b[(i+2)%3]-a[(i+2)%3]*b[(i+1)%3])%P for i in range(3))
def independent(cols):return rank(cols)==len(cols)
E=[tuple(int(i==j) for i in range(5)) for j in range(5)]
counts=dict(configurations=0,endpoint_sector_identities=0,quintic_Newton_checks=0,lower_middle_checks=0,near_top_checks=0,top_checks=0,fixed_R_unit_checks=0)
for case in range(64):
 core=[rng.randrange(8) for _ in range(5)]
 if case%8==0:core=[7]*5
 if case%13==0:core=[0]*5
 lm=[1,2,4]+[rng.randrange(1,8) for _ in range(case%3)]
 rm=[1,2,4,8,16]+[rng.randrange(1,32)]
 w=[rng.randrange(1,5) for _ in rm]
 K=[tuple(rng.randrange(1,100000) if mask>>j&1 else 0 for j in range(3)) for mask in core]
 Kc=[tuple(K[i][a] for i in range(5)) for a in range(3)]
 L=[tuple(rng.randrange(1,100000) if mask>>j&1 else 0 for j in range(3)) for mask in lm]
 R=[tuple(rng.randrange(1,100000) if mask>>j&1 else 0 for j in range(5)) for mask in rm]
 q=sum(independent(vs) for vs in combinations(L,3));require(q>0,'q')
 normals=[cross(*vs) for vs in combinations(L,2) if independent(vs)]
 VV=[tuple(sum(row[j]*v[j] for j in range(3))%P for row in K) for v in normals]
 def sector(J,ne,nv):
  if ne<0 or nv<0:return 0
  return sum(independent([R[j] for j in J]+list(es)+list(vs)) for es in combinations(E,ne) for vs in combinations(VV,nv))
 def left_one(J,ne):
  if ne<0:return 0
  return sum(rank([Kc[c]+(ell[c],) for c in range(3)]+[R[j]+(0,) for j in J]+[e+(0,) for e in es])==6 for ell in L for es in combinations(E,ne))
 def left_zero(J,ne):
  if ne<0:return 0
  return sum(rank(Kc+[R[j] for j in J]+list(es))==5 for es in combinations(E,ne))
 Csec=[0]*6;bb=[0]*6
 for j in range(6):
  for J in combinations(range(len(R)),j):
   wt=prod(w[i] for i in J)
   V=sector(J,5-j,0);X=sector(J,4-j,1);N=left_one(J,3-j);Z=left_zero(J,2-j)
   Csec[j]+=wt*(q*V+X+N+Z)
   bb[j]+=wt*sum(q**(5-j-nv)*sector(J,5-j-nv,nv) for nv in range(min(3,5-j)+1))
   if j==1:
    W=sum(rank([R[J[0]]]+list(es))==3 and rank(Kc+[R[J[0]]]+list(es))==5 for es in combinations(E,2))
    require(q*V+X>=N+Z-2*W,('unit',case,J,V,X,N,Z,W,q))
    counts['fixed_R_unit_checks']+=1
 rows=core+lm;Bcols=[sum(1<<i for i,row in enumerate(rows) if row>>j&1) for j in range(3)]
 C=[sum(prod(w[i] for i in J)*len(endpoints(tuple(Bcols+[rm[i] for i in J]))) for J in combinations(range(len(R)),j)) for j in range(6)]
 require(Csec==C,('sector',case,Csec,C));counts['endpoint_sector_identities']+=6
 require(bb[2]<=q*q*C[2],('b2 upper',case))
 require(12*bb[3]>=11*q*C[3],('b3 lower',case))
 require(8*bb[1]>=7*q**3*C[1],('b1 lower',case))
 require(bb[2]**2>=2*bb[1]*bb[3],('Newton',case));counts['quintic_Newton_checks']+=1
 require(48*C[2]**2>=77*C[1]*C[3],('middle',case));counts['lower_middle_checks']+=1
 require(4*C[3]**2>7*C[2]*C[4],('near top',case));counts['near_top_checks']+=1
 require(24*C[4]**2>=55*C[3]*C[5],('top',case));counts['top_checks']+=1
 counts['configurations']+=1
 if case%8==7:print('completed',case+1,flush=True)
out=dict(scope='Exact endpoint and represented finite-field regression only; no finite grid is used as proof',field_prime=P,all_pass=True,**counts)
expected=Path(__file__).resolve().parent.parent/'data'/'verify_five_by_three.json'
require(out==json.loads(expected.read_text()),'stored regression summary mismatch')
print(json.dumps(out,indent=2))
