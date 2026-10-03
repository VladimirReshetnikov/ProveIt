#!/usr/bin/env python3
"""Corroboration of the ordinary three-tail zero-rank Hessian lemma."""
if not __debug__: raise SystemExit('Run without -O; assertions are required')
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,product
import argparse,hashlib,json,random,time
parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);args=parser.parse_args()
start=time.monotonic();cases=0;zeros=0;full=0;minors=0
rng=random.Random(19860419)
def det3(m):return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0])
def check(types,weights):
 global cases,zeros,full,minors
 r=[sum((w for t,w in zip(types,weights) if t>>i&1),F(0)) for i in range(3)]
 n=[[F(0)]*3 for i in range(3)]
 for i in range(3):
  n[i][i]=2*r[i]**2
  for j in range(i):
   h=sum((w for t,w in zip(types,weights) if t>>i&1 and t>>j&1),F(0))
   q=sum((w*w for t,w in zip(types,weights) if t>>i&1 and t>>j&1),F(0))
   pair=sum((weights[a]*weights[b] for a,b in combinations(range(len(types)),2) if ((types[a]>>i&1 and types[b]>>j&1) or (types[a]>>j&1 and types[b]>>i&1))),F(0))
   assert pair==r[i]*r[j]-(h*h+q)/2
   n[i][j]=n[j][i]=2*r[i]*r[j]-3*pair
   if r[i] and r[j]:assert n[i][j]/r[i]/r[j]==F(3,2)*(h*h+q)/r[i]/r[j]-1
 for i in range(3):assert n[i][i]>=0
 for i,j in combinations(range(3),2):assert n[i][i]*n[j][j]-n[i][j]**2>=0
 assert det3(n)>=0
 cases+=1;zeros+=any(w==0 for w in weights);full+=all(r);minors+=7
for size in range(5):
 for types in product(range(1,8),repeat=size):
  for variant in range(2):
   weights=[F((i+1)*(i+2),i+3) if variant==0 else F((i+sum(types))%4,1+(i%3)) for i in range(size)]
   check(types,weights)
for k in range(1000):
 size=rng.randrange(0,13);types=[rng.randrange(1,8) for _ in range(size)];weights=[F(rng.randrange(0,11),rng.randrange(1,7)) for _ in range(size)];check(types,weights)
args.output_dir.mkdir(parents=True,exist_ok=True)
receipt={'status':'PASS','cases':cases,'cases_with_zero_weights':zeros,'cases_with_all_R_positive':full,'principal_minors_checked':minors,'literal_pair_support_formula':'PASS','matrix_normalization_identity':'PASS','seconds':round(time.monotonic()-start,3)}
(args.output_dir/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
