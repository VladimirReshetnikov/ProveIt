#!/usr/bin/env python3
if not __debug__:raise SystemExit('Run without -O; assertions are required')
from itertools import combinations
from pathlib import Path
from collections import defaultdict
import argparse,json,time
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);a=pa.parse_args();start=time.monotonic()
# Left order p0,p1,p2,c,x0,x1. Right order q0,q1,q2,y0,y1,y2,h.
rows=[(1<<i)|(1<<(3+i))|(1<<6)for i in range(3)]+[7,1,2]
w=[1,1,1,4,4,4,1]
gamma=[0]*7;terms=defaultdict(int);supports=0;candidates=0
# Literal Hall: every subset of selected tails must have at least its cardinality
# many neighbors among the selected heads. No enumeration of matching witnesses.
for tm in range(1<<6):
 k=tm.bit_count()
 for hs in combinations(range(7),k):
  hm=sum(1<<h for h in hs);candidates+=1
  good=True;sub=tm
  while sub:
   neighbors=0
   for i in range(6):
    if sub>>i&1:neighbors|=rows[i]
   if (neighbors&hm).bit_count()<sub.bit_count():good=False;break
   sub=(sub-1)&tm
  if not good:continue
  weight=1
  for h in hs:weight*=w[h]
  gamma[k]+=weight;supports+=1
  if tm==15: # select p0,p1,p2,c and set the two other tail variables to zero
   exps=tuple(0 if hm>>i&1 else 1 for i in range(3))+(3-sum(h>=3 for h in hs),)
   assert sum(exps)==2
   terms[exps]+=weight
expected={(2,0,0,0):0,(0,2,0,0):0,(0,0,2,0):0,(0,0,0,2):13}
for i,j in combinations(range(3),2):
 e=[0]*4;e[i]=e[j]=1;expected[tuple(e)]=112
for i in range(3):
 e=[0]*4;e[i]=e[3]=1;expected[tuple(e)]=44
expected={k:v for k,v in expected.items()if v}
assert dict(terms)==expected,dict(terms)
assert gamma==[1,23,195,743,1234,744,112],gamma
hessian=[[0,112,112,44],[112,0,112,44],[112,112,0,44],[44,44,44,26]]
# The 2-dimensional restriction x0=x1=x2=x has Hessian [[672,132],[132,26]].
assert 672>0 and 672*26-132**2==48
assert 132**2-4*336*13==-48
# The other two old-variable directions are negative with eigenvalue -112.
for v in ([1,-1,0,0],[1,0,-1,0]):assert [sum(hessian[i][j]*v[j]for j in range(4))for i in range(4)]==[-112*x for x in v]
# Verify the explicit saturating matching, hence matching rank exactly six.
assignment=[3,4,5,2,0,1]
assert len(set(assignment))==6 and all(rows[i]>>h&1 for i,h in enumerate(assignment))
# Exact actual-order-six Newton inequalities; all are strict.
from fractions import Fraction as F
from math import comb
gaps=[F(gamma[k]**2)-F(comb(6,k)**2,comb(6,k-1)*comb(6,k+1))*gamma[k-1]*gamma[k+1]for k in range(1,6)]
assert all(g>0 for g in gaps)
rec={'status':'PASS','left_rows':rows,'right_weights':w,'endpoint_candidates':candidates,'feasible_endpoint_pairs':supports,'gamma':gamma,'quadratic_terms':{','.join(map(str,k)):v for k,v in sorted(terms.items())},'principal_hessian':hessian,'hessian_inertia':[2,2,0],'diagonal_discriminant':-48,'matching_rank':6,'strict_scalar_rank_six_ULC_gaps':[str(g)for g in gaps],'scope':'Failure of multivariate Lorentzianity only, not scalar ULC','seconds':round(time.monotonic()-start,3)}
a.output_dir.mkdir(parents=True,exist_ok=True);(a.output_dir/'verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
