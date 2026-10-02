#!/usr/bin/env python3
"""Finite all-state suffix checks; this is not a preservation theorem."""
from functools import lru_cache
from pathlib import Path
import json

def children(s,u,k):
    for i in range(s): yield s-1,u+(i>=k),i
    for i in range(s,s+u): yield s+1,u-(i<k),i+1

@lru_cache(None)
def F(n,s,u,k):
    if n==0:return 1
    return sum(F(n-1,*state) for state in children(s,u,k))

bad=[];states=0;tests=0
for m in range(1,9):
    for s in range(m):
        u=m-s
        for k in range(m):
            states+=1
            assert sum(ss+uu for ss,uu,kk in children(s,u,k))==m*m+u-k
            f=[F(n,s,u,k) for n in range(17)]
            for n in range(1,16):
                tests+=1
                if (n+1)*f[n]**2<n*f[n-1]*f[n+1]:bad.append([n,s,u,k])

result=dict(scope='Finite checks only; no general preservation theorem.',
            states=states,logconcavity_tests=tests,max_m=8,max_center=15,
            failures=bad,moment_identity_checked=True)
(Path(__file__).resolve().parent/'generic-logconcavity.json').write_text(
    json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
