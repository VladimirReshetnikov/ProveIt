#!/usr/bin/env python3
"""Finite inductive zero/one/at-least-two invariants for literal Prog254.

Each register carries a subset of {0,1,>=2}, encoded by bits 1,2,4. Joins
are union; transfer functions are exact on each atom except the necessary
positive-decrement union for >=2. All accepted invariants are checked again
for initial inclusion and closure under every allowed branch.
"""
from collections import deque,Counter
from pathlib import Path
import json,time
from program import sites,lookup,site_map,audit

ROOT=Path(__file__).resolve().parent
Z,O,M=1,2,4

def inc(mask):
    return (O if mask&Z else 0)|(M if mask&(O|M) else 0)

def dec(mask):
    return (Z if mask&O else 0)|((O|M) if mask&M else 0)

def atom(n):return Z if n==0 else O if n==1 else M

def transfers(p,vector):
    _,op,r,pos,zero=site_map[p]
    if op=='CH':return
    if op=='CD':
        if vector[r]&Z:
            v=list(vector);v[r]=Z
            yield lookup(zero)[0],tuple(v),'zero'
        if vector[r]&(O|M):
            v=list(vector);v[r]=dec(vector[r]&(O|M))
            yield lookup(pos)[0],tuple(v),'positive'
    else:
        v=list(vector)
        if op=='CI':v[r]=inc(v[r])
        yield lookup(pos)[0],tuple(v),op

def solve(initial):
    start=lookup('')[0];invariant={start:tuple(initial)}
    queue=deque([start]);queued={start};iterations=0
    while queue:
        p=queue.popleft();queued.remove(p);iterations+=1
        for nxt,v,_ in transfers(p,invariant[p]):
            old=invariant.get(nxt,(0,)*9)
            joined=tuple(a|b for a,b in zip(old,v))
            if joined!=old:
                invariant[nxt]=joined
                if nxt not in queued:queue.append(nxt);queued.add(nxt)
    return invariant,iterations

def check(initial,invariant):
    assert all(a&~b==0 for a,b in zip(initial,invariant[lookup('')[0]]))
    checked=0
    for p,v in invariant.items():
        assert p in site_map and len(v)==9 and all(0<x<8 for x in v)
        for nxt,w,branch in transfers(p,v):
            assert nxt in invariant
            assert all(a&~b==0 for a,b in zip(w,invariant[nxt])),(p,nxt,branch)
            checked+=1
    return checked

def summarize(invariant):
    unreachable=[];guards=[];zero_fields=[];masks=Counter()
    for p,op,r,_,_ in site_map.values():
        if p not in invariant:
            unreachable.append(dict(pc=p,operation=op,logical_argument=r))
            continue
        v=invariant[p];masks.update(v)
        if op=='CD':
            if not v[r]&Z:guards.append(dict(pc=p,logical_argument=r,impossible='zero',mask=v[r]))
            if not v[r]&(O|M):guards.append(dict(pc=p,logical_argument=r,impossible='positive',mask=v[r]))
        known=[r for r,m in enumerate(v) if m==Z]
        if known:zero_fields.append(dict(pc=p,logical_zero_registers=known))
    return dict(reachable_leaf_count=len(invariant),unreachable_leaf_count=len(unreachable),
                impossible_guard_count=len(guards),unreachable_leaves=unreachable,
                impossible_guards=guards,known_zero_fields=zero_fields,
                mask_frequencies=dict(masks))

if __name__=='__main__':
    began=time.monotonic()
    # The same sufficient root class as six_nonformula_path_iff, with all six
    # numerical fields arbitrary and the formula/cache/stack fields zero.
    initial=(7,1,1,7,7,1,7,7,7)
    inv,iterations=solve(initial);checked=check(initial,inv)
    result=dict(status='PASS',initial_masks=initial,iterations=iterations,
                checked_transfers=checked,seconds=time.monotonic()-began,
                interpretation={'1':'zero','2':'one','4':'at least two'},
                **summarize(inv),invariant={p:list(v) for p,v in sorted(inv.items())})
    (ROOT.parent/'data/source-abstract-invariant.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
        ('unreachable_leaves','impossible_guards','known_zero_fields','invariant')},indent=2))
