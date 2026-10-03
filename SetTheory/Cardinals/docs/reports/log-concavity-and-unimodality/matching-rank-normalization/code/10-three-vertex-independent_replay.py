#!/usr/bin/env python3
"""Independent determinant reconstruction via the five-term symmetric formula."""
from collections import defaultdict
from pathlib import Path
from hashlib import sha256
import json
n=11;zero=(0,)*n

def mon(i):
 v=list(zero);v[i]=1;return {tuple(v):1}
def plus(*ps):
 r=defaultdict(int)
 for p in ps:
  for e,c in p.items():r[e]+=c
 return {e:c for e,c in r.items() if c}
def times(p,q):
 r=defaultdict(int)
 for e,c in p.items():
  for f,d in q.items():r[tuple(e[i]+f[i] for i in range(n))]+=c*d
 return {e:c for e,c in r.items() if c}
def scale(p,c):return {e:c*v for e,v in p.items() if c*v}
def square(p):return times(p,p)
X=[mon(i) for i in range(n)]
# Explicit neighborhood linear forms, independently of the discovery loops.
c1=plus(X[0],X[3],X[4],X[5],X[6],X[9],X[10])
c2=plus(X[1],X[3],X[4],X[7],X[8],X[9],X[10])
c3=plus(X[2],X[5],X[6],X[7],X[8],X[9],X[10])
d12=plus(scale(times(c1,c2),-2),scale(square(plus(X[3],X[4],X[9],X[10])),3),scale(plus(square(X[3]),square(X[9])),3))
d13=plus(scale(times(c1,c3),-2),scale(square(plus(X[5],X[6],X[9],X[10])),3),scale(plus(square(X[5]),square(X[9])),3))
d23=plus(scale(times(c2,c3),-2),scale(square(plus(X[7],X[8],X[9],X[10])),3),scale(plus(square(X[7]),square(X[9])),3))
a,b,c=[scale(square(x),4) for x in [c1,c2,c3]]
f=plus(times(times(a,b),c),scale(times(times(d12,d13),d23),2),scale(times(a,square(d23)),-1),scale(times(b,square(d13)),-1),scale(times(c,square(d12)),-1))
if not f or min(f.values())<=0 or any(sum(e)!=6 for e in f):raise RuntimeError('determinant failed')
rec=[[list(e),v] for e,v in sorted(f.items())];h=sha256(json.dumps(rec,separators=(',',':')).encode()).hexdigest()
primary=json.loads((Path(__file__).parents[1]/'data'/'determinant.json').read_text())
if rec!=primary['coefficients']:raise RuntimeError('independent expansion differs')
out=dict(algorithm='Explicit neighborhood forms and abc+2def-af²-be²-cd², using only standard-library integer arithmetic',coefficient_count=len(rec),minimum_coefficient=min(f.values()),maximum_coefficient=max(f.values()),canonical_sha256=h,all_pass=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
