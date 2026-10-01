#!/usr/bin/env python3
"""Enumerate every support/normal profile from common-coordinate ratio partitions."""
from itertools import permutations
from pathlib import Path
import json
def partitions(xs):
    if not xs:yield [];return
    x,*rest=xs
    for p in partitions(rest):
        yield [[x]]+[b[:] for b in p]
        for i in range(len(p)):
            q=[b[:] for b in p];q[i]=[x]+q[i];yield q
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def mask(v):return sum(1<<i for i,x in enumerate(v) if x)
def permute(x,p):return sum(1<<p[i] for i in range(3) if x>>i&1)
def canonical(profile):
    a,b,c=profile
    return min((x,y,z) for p in permutations(range(3)) for x,y,z in [(permute(a,p),permute(b,p),permute(c,p)),(permute(b,p),permute(a,p),permute(c,p))])
allprofiles=set();examples={}
for a in range(1,8):
 for b in range(1,8):
  common=[i for i in range(3) if (a&b)>>i&1]
  for part in partitions(common):
   v=[int(a>>i&1) for i in range(3)];w=[int(b>>i&1) for i in range(3)]
   for k,block in enumerate(part,1):
    for i in block:v[i]=k
   n=mask(cross(v,w))
   if not n:continue
   profile=(a,b,n);allprofiles.add(profile);examples.setdefault(canonical(profile),(v,w))
expected=[(1,2,4),(1,3,4),(3,3,4),(4,3,3),(4,7,3),(3,7,3),(7,7,3),(3,5,7),(3,7,7),(7,7,7)]
orbits={canonical(x) for x in allprofiles}
if len(orbits)!=10 or orbits!={canonical(x) for x in expected}:raise RuntimeError("Orbit classification mismatch")
out={'status':'passed','labeled_profiles':len(allprofiles),'orbits':len(orbits),'representatives':expected,'canonical_representatives':sorted(orbits)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

