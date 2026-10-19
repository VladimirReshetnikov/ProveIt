"""Small exact source-DAG library used by the present dictionary experiment.

Boundary and path recurrences follow the attributed Source103 and latest
Sub237 exact_reassociate.py. Input is the exact 237-candidate source DAG.
No binary transition or runtime theorem is asserted by these helpers.
"""
from pathlib import Path
from functools import cache
import json

J=json.loads(Path(__file__).with_name('boundary_source_input.json').read_text())
S=[tuple(x)for x in J['structures']]
I={x:i for i,x in enumerate(S)}
ROOT=J['root']

def cons(a,b):
    p=(a,b)
    if p not in I:I[p]=len(S);S.append(p)
    return I[p]

@cache
def paths(n):
    x=S[n]
    if isinstance(x[0],str):return (('',x[0],x[1]),)
    return tuple((str(b)+p,o,r)for b in (0,1)for p,o,r in paths(x[b]))

@cache
def boundary(n):
    x=S[n]
    if isinstance(x[0],str):
        return (1,0,False)if x[0]=='CD'else(x[1],0,False)if x[0]=='CB'else(0,x[1],False)if x[0]=='CC'else(0,0,x[0]=='CH')
    a,b=map(boundary,x)
    return (max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2]or b[2])

def closed(n):return boundary(n)==(0,0,False)

@cache
def live(n):
    if isinstance(S[n][0],str):return frozenset([n])
    return frozenset([n])|live(S[n][0])|live(S[n][1])

@cache
def lead(n):return 1+lead(S[n][0])if isinstance(S[n][0],int)else 0
@cache
def zero_run(n):return max(1+lead(S[n][0]),zero_run(S[n][0]),zero_run(S[n][1]))if isinstance(S[n][0],int)else 0
@cache
def depth(n):return 1+max(depth(S[n][0]),depth(S[n][1]))if isinstance(S[n][0],int)else 0

def score(n):return len(live(n)),zero_run(n),depth(n)

def replace(root,n,alt):
    @cache
    def go(k):
        if k==n:return alt
        if isinstance(S[k][0],str):return k
        return cons(*map(go,S[k]))
    return go(root)
