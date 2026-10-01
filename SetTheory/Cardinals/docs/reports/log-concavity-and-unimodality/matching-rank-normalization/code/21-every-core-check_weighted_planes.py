"""Independent exact weighted plane-incidence regression."""
from itertools import combinations
from math import gcd
from random import Random
from collections import defaultdict
from pathlib import Path
import json

def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def det(a,b,c):return dot(a,cross(b,c))
def line(v):
    g=0
    for x in v:g=gcd(g,x)
    v=tuple(x//g for x in v)
    return tuple(-x for x in v) if next(x for x in v if x)<0 else v
rng=Random(710261)
cases=0
for n in range(3,13):
    for trial in range(60):
        while True:
            E=[tuple(rng.randint(-3,3) for _ in range(3)) for _ in range(n)]
            if all(any(v) for v in E) and any(det(*vs) for vs in combinations(E,3)):break
        weights=[rng.randint(1,11) for _ in E]
        while True:
            normal=tuple(rng.randint(-3,3) for _ in range(3))
            if any(normal):break
        beta=sum(w for v,w in zip(E,weights) if dot(v,normal))
        q=sum(weights[i]*weights[j]*weights[k] for i,j,k in combinations(range(n),3) if det(E[i],E[j],E[k]))
        classes=defaultdict(int)
        for i,j in combinations(range(n),2):
            pair_normal=cross(E[i],E[j])
            if not any(pair_normal):continue
            direction=cross(normal,pair_normal)
            if any(direction):classes[line(direction)]+=weights[i]*weights[j]
        h=sum(classes.values());Q=h*h-sum(v*v for v in classes.values())
        if 2*Q<3*q*beta:raise ArithmeticError((E,weights,normal,2*Q,3*q*beta))
        cases+=1
out={'passed':True,'weighted_plane_cases':cases,'activity_range':[1,11],'left_size_range':[3,12],'method':'direct exact determinant and line-class counts, no Hessian computation'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
