#!/usr/bin/env python3
if not __debug__: raise SystemExit('Run without -O; assertions are required')
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse,json,random,time
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);args=pa.parse_args();start=time.monotonic();rng=random.Random(2671001)
cases=0;zero=0;pairs=0;psds=0

def psd(m):
 m=[list(a) for a in m]
 while m:
  assert all(m[i][i]>=0 for i in range(len(m)))
  inds=[i for i in range(len(m)) if m[i][i]>0]
  if not inds:
   assert all(x==0 for row in m for x in row);return
  k=inds[0];ids=[i for i in range(len(m)) if i!=k];p=m[k][k]
  m=[[m[i][j]-m[i][k]*m[k][j]/p for j in ids]for i in ids]

for r in range(2,9):
 for trial in range(400):
  n=rng.randrange(0,15);types=[rng.randrange(1,1<<r)for _ in range(n)];w=[Q(rng.randrange(0,11),rng.randrange(1,7))for _ in range(n)]
  R=[sum((v for t,v in zip(types,w)if t>>i&1),Q(0))for i in range(r)];N=[[Q(0)]*r for _ in range(r)];good=[i for i in range(r)if R[i]]
  A=[[Q(0)]*len(good)for _ in good];C=[[Q(0)]*len(good)for _ in good]
  for i in range(r):
   N[i][i]=(r-1)*R[i]**2
   for j in range(i):
    h=sum((v for t,v in zip(types,w)if t>>i&1 and t>>j&1),Q(0));q=sum((v*v for t,v in zip(types,w)if t>>i&1 and t>>j&1),Q(0))
    p=sum((w[y]*w[z]for y,z in combinations(range(n),2)if (types[y]>>i&1 and types[z]>>j&1)or(types[z]>>i&1 and types[y]>>j&1)),Q(0));pairs+=1
    assert p==R[i]*R[j]-(h*h+q)/2
    N[i][j]=N[j][i]=(r-1)*R[i]*R[j]-r*p
  for ii,i in enumerate(good):
   for jj,j in enumerate(good):
    h=sum((v for t,v in zip(types,w)if t>>i&1 and t>>j&1),Q(0));q=sum((v*v for t,v in zip(types,w)if t>>i&1 and t>>j&1),Q(0))
    A[ii][jj]=h*h/(R[i]*R[j]);C[ii][jj]=Q(1)if i==j else q/(R[i]*R[j])
    assert N[i][j]/R[i]/R[j]==Q(r,2)*(A[ii][jj]+C[ii][jj])-1
  psd(N);psd([[v-Q(1,r)for v in row]for row in A]);psd([[v-Q(1,r)for v in row]for row in C]);psds+=3
  cases+=1;zero+=any(v==0 for v in w)or len(good)<r
rec={'status':'PASS','tail_counts':list(range(2,9)),'weighted_graph_cases':cases,'cases_with_zero_weights_or_zero_R':zero,'literal_pair_recounts':pairs,'exact_PSD_checks':psds,'seconds':round(time.monotonic()-start,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'general_verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
