#!/usr/bin/env python3
"""Finite experiments for entropy-optimal prime factorizations.
Only Python's standard library is used. No experiments are assumptions of the proof.
"""
from itertools import product
from math import gcd, prod, factorial, log
from random import Random
import json
from pathlib import Path


def units(q):
    return [a for a in range(q) if gcd(a,q)==1]


def partitions(seq):
    if not seq:
        yield ()
        return
    x, *rest = seq
    for part in partitions(rest):
        yield ((x,),) + part
        for i in range(len(part)):
            yield part[:i] + ((x,) + part[i],) + part[i+1:]


def multi(ks):
    return factorial(sum(ks)) // prod(factorial(k) for k in ks)


def entropy(ks):
    n = sum(ks)
    return -sum(k/n*log(k/n) for k in ks if k)


def obstruction(qs, ks):
    g = gcd(*qs)
    return [dict(partition=[list(b) for b in p], required=prod(len(units(gcd(*(qs[j] for j in b)))) for b in p)//len(units(g)),
                 assignments=multi([sum(ks[j] for j in b) for b in p]))
            for p in partitions(list(range(len(qs)))) if len(p)>1]


def isprime(n):
    return n>=2 and all(n%d for d in range(2,int(n**.5)+1))


def reachable(qs, ps, ks):
    """Exact dynamic program over (quota counts, residue vector)."""
    r=len(qs)
    dp={(0,)*r:{tuple(1%q for q in qs)}}
    for p in ps:
        new={}
        for counts, vals in dp.items():
            for j in range(r):
                if counts[j]==ks[j]: continue
                cc=counts[:j]+(counts[j]+1,)+counts[j+1:]
                target=new.setdefault(cc,set())
                q=qs[j]
                target.update(v[:j]+(v[j]*p%q,)+v[j+1:] for v in vals)
        dp=new
    return dp.get(tuple(ks),set())


def compatible(qs, ps):
    g=gcd(*qs)
    target=prod(ps)%g
    return {v for v in product(*(units(q) for q in qs)) if prod(v)%g==target}


def find_example(qs, ks, seed):
    rng=Random(seed)
    candidates=[p for p in range(101,500) if isprime(p) and all(gcd(p,q)==1 for q in qs)]
    for trial in range(1,201):
        ps=sorted(rng.sample(candidates,sum(ks)))
        got=reachable(qs,ps,ks); goal=compatible(qs,ps)
        assert got<=goal
        if got==goal:
            return dict(moduli=qs, quotas=ks, primes=ps, trial=trial, support=len(got), compatible=len(goal), partitions=obstruction(qs,ks))
    raise RuntimeError((qs,ks))


def repair_example():
    """Verify the pair-repair inclusion simultaneously for two quota profiles."""
    qs=(7,9,21); ps=(11,13,17,19,23,29); a=(31,37); b=(41,43)
    g=gcd(*qs)
    r=len(qs)
    base=(a[0]%qs[0],a[1]%qs[1],prod(b)%qs[2])
    alt=(b[0]%qs[0],b[1]%qs[1],prod(a)%qs[2])
    v=tuple(alt[i]*pow(base[i],-1,qs[i])%qs[i] for i in range(r))
    assert prod(v)%g==1%g
    newps=ps+a+b
    results=[]
    for ks in ((2,2,2),(3,1,2)):
        old=reachable(qs,ps,ks)
        oldmiss=compatible(qs,ps)-old
        nk=tuple(ks[j]+(1 if j<r-1 else r-1) for j in range(r))
        new=reachable(qs,newps,nk)
        newmiss=compatible(qs,newps)-new
        def shift(S,u): return {tuple(x*y%q for x,y,q in zip(w,u,qs)) for w in S}
        assert newmiss <= shift(oldmiss & shift(oldmiss,v),base)
        results.append(dict(old_quotas=ks,new_quotas=nk,old_missing=len(oldmiss),new_missing=len(newmiss),bound=len(oldmiss&shift(oldmiss,v))))
    return dict(moduli=qs,base_primes=ps,pair_a=a,pair_b=b,checks=results)


def main():
    bad=obstruction((101,101,101),(6,6,1))
    full=next(x for x in bad if len(x['partition'])==3)
    assert full['assignments']>=full['required']
    assert any(x['assignments']<x['required'] for x in bad)
    result={
      'warning':'Finite checks only, not a proof of the asymptotic theorem.',
      'coarsening_obstruction':bad,
      'complete_examples':[
        find_example((13,13,13),(3,3,3),20261127),
        find_example((12,18,30),(3,3,3),20261128),
        find_example((15,21,35),(4,4,4),20261129),
      ],
      'repair_inclusion':repair_example(),
    }
    print(json.dumps(result,indent=2))
    Path(__file__).with_name('experiment_results.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__': main()
