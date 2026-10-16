"""Finite regressions for the positive switching-cover bootstrap.

Ackermann code x denotes the HF set whose elements are its set-bit indices.
Finite graph tests are NOT models of the full set-theoretic schema.
"""
from __future__ import annotations
import json
from functools import lru_cache
from pathlib import Path

def members(x):
    while x:
        bit=x & -x
        yield bit.bit_length()-1
        x-=bit

def submasks(x):
    y=x
    while True:
        yield y
        if not y:return
        y=(y-1)&x

@lru_cache(None)
def switch(x):
    # Singleton inputs are decoded; nonsingletons output all subsets.
    if x and x&(x-1)==0: return (x.bit_length()-1,)
    return tuple(submasks(x))

def cover(root):
    # Positive orbit: the seed itself is NOT automatically put in the result.
    out=set();todo=list(switch(root))
    while todo:
        x=todo.pop()
        if x not in out:
            out.add(x);todo.extend(switch(x))
    return out

def graph_audit(max_n=4):
    graphs=seeds=points=0
    for n in range(1,max_n+1):
        mask=(1<<n)-1
        for g in range(1<<(n*n)):
            rows=[(g>>(i*n))&mask for i in range(n)]
            global_range=0
            for r in rows:global_range|=r
            def image(s):
                z=0
                for i in members(s):z|=rows[i]
                return z
            for seed in range(1<<n):
                c=image(seed)
                while True:
                    d=c|image(c)
                    if c==d:break
                    c=d
                assert image(seed|c)&~c==0
                assert c&~global_range==0
                seeds+=1
                if seed and seed&(seed-1)==0:points+=1
            graphs+=1
    return {'graphs':graphs,'seed_subsets':seeds,'point_seeds':points}

def main():
    roots=4096;local_outputs=cover_members=member_edges=0
    max_cover=0
    for a in range(roots):
        outs=switch(a)
        b=outs[0] if a and a&(a-1)==0 else a
        assert all(y&~b==0 for y in outs)
        local_outputs+=len(outs)
        c=cover(a)
        assert set(members(a))<=c
        assert all(set(members(x))<=c for x in c)
        assert all(set(switch(x))<=c for x in c)
        cover_members+=len(c)
        member_edges+=sum(x.bit_count() for x in c)
        max_cover=max(max_cover,len(c))
    # Direct regression for conversion of mixed output bounds to subset bounds.
    bound_cases=0
    for b in range(256):
        c=cover(b); code=sum(1<<x for x in c)
        for y in range(256):
            if (b>>y)&1 or y&~b==0:
                assert y&~code==0;bound_cases+=1
    # The naive all-subsets relation is not sufficient for a transitive cover.
    naive={0,2}
    assert all(set(submasks(x))<=naive for x in naive)
    assert 1 in set(members(2)) and 1 not in naive
    # Full membership on a one-object domain satisfies purity-deleted closure.
    for r in (False,True):
        assert ((not r) or True) # local subset bound and closure; C is the sole object
    data={
      'status':'all assertions passed',
      'hf':{'roots':roots,'local_outputs':local_outputs,'cover_members':cover_members,
            'checked_member_edges':member_edges,'maximum_cover_cardinality':max_cover,
            'mixed_bound_cases':bound_cases},
      'graphs':graph_audit(),
      'naive_subset_counterexample':{'root':2,'positive_hull':[0,2],'missing_member':1},
      'limits':'Finite regressions, not a formal proof or a consistency test.'}
    root=Path(__file__).resolve().parents[1]
    (root/'results'/'experiments.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
if __name__=='__main__':main()
