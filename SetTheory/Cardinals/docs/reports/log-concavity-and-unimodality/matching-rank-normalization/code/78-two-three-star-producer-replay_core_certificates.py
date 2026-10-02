#!/usr/bin/env python3
"""Solver-free rational replay of all 26 core-mask middle-gap certificates."""
if not __debug__:raise SystemExit('Run without -O; assertions are required.')
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
from math import comb
import hashlib,json,time
ROOT=Path(__file__).resolve().parent
DIM=8;ZERO=(0,)*DIM
def add(p,q,scale=1):
 r=dict(p)
 for a,c in q.items():r[a]=r.get(a,0)+scale*c
 return{a:c for a,c in r.items()if c}
def mul(p,q):
 r={}
 for a,c in p.items():
  for b,d in q.items():
   x=tuple(v+w for v,w in zip(a,b));r[x]=r.get(x,0)+c*d
 return{a:c for a,c in r.items()if c}
def orbit(mask):
 return min(sum(((mask>>(3*rp[i]+cp[j]))&1)<<(3*i+j)for i in range(2)for j in range(3))for rp in [(0,1),(1,0)]for cp in permutations(range(3)))
def core_rank(mask,I,J):
 def rec(rows,used):
  if not rows:return 0
  i,*rest=rows;best=rec(rest,used)
  for j in range(3):
   if J>>j&1 and not used>>j&1 and mask>>(3*i+j)&1:best=max(best,1+rec(rest,used|1<<j))
  return best
 return rec([i for i in range(2)if I>>i&1],0)
def gamma(mask):
 g=[{}for _ in range(6)]
 for I in range(4):
  for J in range(8):
   i,j=I.bit_count(),J.bit_count();rank=core_rank(mask,I,J)
   for k in range(6):
    nx,ny=k-i,k-j
    if not(0<=nx<=3 and 0<=ny<=2 and 0<=i+j-k<=rank):continue
    exp=tuple((I>>a)&1 for a in range(2))+tuple((J>>a)&1 for a in range(3))+(int(nx==2),int(nx==3),int(ny==2))
    g[k][exp]=g[k].get(exp,0)+1
 return g
def cone(p,k):
 dv=max(a[5]+2*a[6]for a in p);dw=max(a[7]for a in p);dz=max(a[6]for a in p)if k==3 else 0;r={}
 for a,c in p.items():
  i,j,l=a[5:];c=F(c,2**(i+l)*6**j)
  for h in range(dv-i-2*j+1):
   for h2 in range(dw-l+1):
    for h3 in range(dz-j+1)if k==3 else [0]:
     e=a[:5]+(i+2*j+h,l+h2,j+h3 if k==3 else 0)
     val=c*comb(dv-i-2*j,h)*comb(dw-l,h2)*(comb(dz-j,h3)if k==3 else 1)
     r[e]=r.get(e,F(0))+val
 return{a:c for a,c in r.items()if c},[dv,dw,dz]
def canonical_hash(p):
 return hashlib.sha256(json.dumps([[list(a),str(c)]for a,c in sorted(p.items())],separators=(',',':')).encode()).hexdigest()
start=time.monotonic();classes={}
for mask in range(64):classes.setdefault(orbit(mask),[]).append(mask)
assert len(classes)==13 and sum(map(len,classes.values()))==64
records=[]
for mask,members in sorted(classes.items()):
 g=gamma(mask)
 for k in [2,3]:
  target,den=cone(add(mul(g[k],g[k]),mul(g[k-1],g[k+1]),-2),k)
  data=json.loads((ROOT/f'core_{mask}_gap_{k}.json').read_text());meta=data['record']
  assert meta['mask']==mask and meta['k']==k and meta['denominator_exponents']==den
  assert meta['terms']==len(target) and meta['negatives']==sum(c<0 for c in target.values())
  assert len(data['squares'])==meta['squares']
  remainder=dict(target)
  for weight,(m,a,b,ratio) in data['squares']:
   weight,ratio=F(weight),F(ratio)
   assert weight>0 and ratio>0
   assert all(len(e)==DIM and all(isinstance(x,int)and x>=0 for x in e)for e in [m,a,b])
   terms=[(tuple(x+2*y for x,y in zip(m,a)),weight*ratio*ratio),(tuple(x+y+z for x,y,z in zip(m,a,b)),-2*weight*ratio),(tuple(x+2*y for x,y in zip(m,b)),weight)]
   for e,c in terms:remainder[e]=remainder.get(e,F(0))-c
  assert all(c>=0 for c in remainder.values()),(mask,k)
  remainder={a:c for a,c in remainder.items()if c}
  assert remainder # strict for positive core and cone variables
  records.append({'mask':mask,'orbit_size':len(members),'gap':k,'target_terms':len(target),'target_negative_terms':meta['negatives'],'squares':len(data['squares']),'positive_remainder_terms':len(remainder),'target_sha256':canonical_hash(target),'remainder_sha256':canonical_hash(remainder),'strict_positive_remainder':True})
receipt={'verdict':'PASS','labeled_core_masks':64,'core_orbits':13,'middle_certificates':len(records),'total_squares':sum(r['squares']for r in records),'total_positive_remainder_terms':sum(r['positive_remainder_terms']for r in records),'all_remainders_nonempty':True,'variables':['u0','u1','q0','q1','q2','V','W','Z'],'records':records,'elapsed_seconds':round(time.monotonic()-start,3)}
(ROOT/'core_exact_replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='records'},indent=2))
