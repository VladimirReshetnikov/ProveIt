#!/usr/bin/env python3
from itertools import combinations,permutations
from math import gcd
from collections import Counter,defaultdict
from pathlib import Path
import json
L=[(1,0,-1,0),(0,1,3,0),(1,0,0,-1),(1,1,0,2),(0,1,0,0),(1,1,0,0)]
def det(a):
 n=len(a);s=0
 for p in permutations(range(n)):
  inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
  v=(-1)**inv
  for i in range(n):v*=a[i][p[i]]
  s+=v
 return s
q=0;bad4=[]
for J in combinations(range(6),4):
 if det([L[i] for i in J]):q+=1
 else:bad4.append(tuple(i+1 for i in J))
beta=0;bad2=[]
for J in combinations(range(6),2):
 if det([L[i][:2] for i in J]):beta+=1
 else:bad2.append(tuple(i+1 for i in J))
classes=defaultdict(list);full=[]
for J in combinations(range(6),3):
 a=[L[i] for i in J]
 normal=[(-1)**k*det([row[:k]+row[k+1:] for row in a]) for k in range(4)]
 if not any(normal):raise RuntimeError(('dependent triple',J))
 x,y=normal[2:];g=gcd(x,y)
 if not g:raise RuntimeError(('zero restriction',J))
 x//=g;y//=g
 if x<0 or (x==0 and y<0):x=-x;y=-y
 classes[(x,y)].append(tuple(i+1 for i in J));full.append((x,y))
D=sum(x*v-y*u!=0 for (x,y),(u,v) in combinations(full,2))
if (q,beta,D)!=(12,12,145):raise RuntimeError((q,beta,D))
if sorted(map(len,classes.values()))!=[1,1,6,6,6]:raise RuntimeError(classes)
# The squarefree degree-six coefficient independently equals 9-10=-1.
Q6=sum(det([L[k] for k in range(6) if k not in J])!=0 and det([L[i][:2] for i in J])!=0 for J in combinations(range(6),2))
D6=0
for S in combinations(range(6),3):
 if 0 not in S:continue
 T=tuple(i for i in range(6) if i not in S)
 def restricted(J):
  a=[L[i] for i in J]
  return [(-1)**k*det([row[:k]+row[k+1:] for row in a]) for k in (2,3)]
 x,y=restricted(S);u,v=restricted(T);D6+=x*v-y*u!=0
if (Q6,D6)!=(9,10):raise RuntimeError((Q6,D6))
out=dict(vectors=L,plane='span(e3,e4)',q=q,beta=beta,D=D,slack=q*beta-D,dependent_four_sets=bad4,noncomplementary_pairs=bad2,restriction_classes=[dict(direction=k,triples=v,mass=len(v)) for k,v in sorted(classes.items())],squarefree_coefficient=dict(q_beta=Q6,D=D6,difference=Q6-D6),all_pass=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
