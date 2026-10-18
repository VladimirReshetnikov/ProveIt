"""Exact rational affine-hull reachability for the literal register program.

Ordinary checked invariant, not a Lean result. Arbitrary rational overapproximation
retains every natural execution; only universally zero/constant guards are pruned.
"""
from pathlib import Path
from collections import deque,Counter
from math import gcd
from functools import reduce,lru_cache
import sys,json,time
sys.path.insert(0,str(Path(__file__).parent/'input'))
import permutation252_phase_analysis as p
sites,cases,targets,first=p.program_graph((Path(__file__).parent/'input/Prog254.v').read_bytes())
by=[[] for _ in sites]
for i,c in enumerate(cases):by[c[0]].append(i)

def norm(v):
    d=reduce(gcd,v)
    if not d:return tuple(v)
    if next(x for x in v if x)!=abs(next(x for x in v if x)):d=-d
    return tuple(x//d for x in v)

def pivot(v):return next(i for i,x in enumerate(v) if x)

@lru_cache(maxsize=200000)
def basis(rows):
    out=[]
    for v in rows:
        for r in out:
            j=pivot(r)
            if v[j]:v=norm(tuple(r[j]*x-v[j]*y for x,y in zip(v,r)))
        if any(v):
            v=norm(v);j=pivot(v)
            out=[norm(tuple(v[j]*x-r[j]*y for x,y in zip(r,v))) if r[j] else r for r in out]
            out.append(v);out.sort(key=pivot)
    return tuple(out)

@lru_cache(maxsize=200000)
def intersect(b,r,k=0):
    # Constrain augmented rows to x_r = k*x_0.
    f=lambda v:v[r+1]-k*v[0]
    bad=next((v for v in b if f(v)),None)
    if bad is None:return b
    a=f(bad); rows=tuple(norm(tuple(a*x-f(v)*y for x,y in zip(v,bad))) for v in b if v is not bad)
    out=basis(rows)
    return out if any(v[0] for v in out) else ()

@lru_cache(maxsize=200000)
def step(b,op,r,z):
    if not b:return ()
    if op=='CD':
        if z:return intersect(b,r)
        if all(v[r+1]==0 for v in b):return ()
    if op not in ('CI','CD'):return b
    delta=1 if op=='CI' else -1
    return basis(tuple(v[:r+1]+(v[r+1]+delta*v[0],)+v[r+2:] for v in b))

def run():
    mask_result=json.loads((Path(__file__).parent/'value-analysis-32.json').read_text())
    masks=mask_result['values']
    use_masks='--reduced' in sys.argv
    def reduce_at(b,site):
        if not use_masks:return b
        if masks[site] is None:return ()
        for r,m in enumerate(masks[site]):
            if m and m&(m-1)==0 and m!=(1<<32):
                b=intersect(b,r,m.bit_length()-1)
                if not b:return ()
        return b
    v=[()]*len(sites);v[first]=((1,)+(0,)*9,);q=deque([first]);queued={first};pops=0;t=time.monotonic()
    while q:
        i=q.popleft();queued.remove(i);pops+=1
        for ci in by[i]:
            dst=targets[ci]
            if dst is None:continue
            _,_,op,r,z=cases[ci];w=step(v[i],op,r,z)
            if not w:continue
            w=reduce_at(w,dst)
            if not w:continue
            old=v[dst];new=basis(old+w)
            if old!=new:
                v[dst]=new
                if dst not in queued:q.append(dst);queued.add(dst)
        if pops%10000==0:print('progress',pops,len(q),time.monotonic()-t,flush=True)
    excluded=[]
    for ci,(site,path,op,r,z) in enumerate(cases):
        w=step(v[site],op,r,z)
        if use_masks and ci in mask_result['excluded']:w=()
        if not w:excluded.append(ci)
        elif targets[ci] is not None:
            w=reduce_at(w,targets[ci])
            assert basis(v[targets[ci]]+w)==v[targets[ci]]
    assert basis(v[first]+((1,)+(0,)*9,))==v[first]
    result=dict(pops=pops,seconds=time.monotonic()-t,excluded=excluded,dimension_counts=dict(Counter(map(len,v))),basis=v)
    (Path(__file__).parent/('affine-analysis-reduced.json' if use_masks else 'affine-analysis.json')).write_text(json.dumps(result))
    print({k:result[k] for k in result if k!='basis'},flush=True)

if __name__=='__main__':run()
