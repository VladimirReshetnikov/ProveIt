#!/usr/bin/env python3
"""Finite interval invariants for the literal register program, with replay checks."""
from pathlib import Path
from collections import deque, Counter
import json, sys

BASE = Path(__file__).resolve().parents[1] / 'reference/context246'
sys.path.insert(0, str(BASE / 'code'))
from rebuild_machines import program_sites

K = 8
INF = K + 1
INITIAL = (3,0,0,0,3,0,0,0,0)

def inc_path(p):
    j = p.rfind('0')
    return p[:j] + '1' + '0' * (len(p)-j-1) if j >= 0 else '0' * len(p)

def strip(p, symbol, count):
    while p and count:
        if p[-1] == symbol: count -= 1
        p = p[:-1]
    return p

def brk(p, n): return inc_path(strip(p, '0', n))
def cont(p, n): return strip(p, '1', n)

def join(a, b):
    if a is None: return b
    return tuple((min(x[0],y[0]),max(x[1],y[1])) for x,y in zip(a,b))

def change(v, r, w):
    return v[:r] + (w,) + v[r+1:]

def transitions(row, v):
    p, op, r = row
    if op == 'CH': return []
    if op == 'CB': return [(brk(p,r), v, 'control')]
    if op == 'CC': return [(cont(p,r), v, 'control')]
    lo, hi = v[r]
    if op == 'CI':
        return [(inc_path(p), change(v,r,(min(K,lo+1), min(INF,hi+1))), 'inc')]
    ans = []
    if lo == 0:
        ans.append((brk(p,1), change(v,r,(0,0)), 'zero'))
    if hi > 0:
        ans.append((inc_path(p), change(v,r,(max(lo,1)-1,hi-1 if hi<INF else INF)), 'positive'))
    return ans

def lookup_function(sites):
    index = {p:i for i,(p,_,_) in enumerate(sites)}
    assert len(index)==len(sites)==6460
    def lookup(p):
        padded = p + '0' * 40
        for j in range(1,41):
            if padded[:j] in index:
                assert all(x == '0' for x in p[j:])
                return index[padded[:j]]
        raise ValueError(p)
    return lookup

def validate_invariants(sites, vals):
    """Check a certificate without trusting its producer or worklist order."""
    assert len(vals)==len(sites)==6460
    checked=[]
    for v in vals:
        if v is None:checked.append(None);continue
        assert isinstance(v,(list,tuple)) and len(v)==9
        row=[]
        for w in v:
            assert isinstance(w,(list,tuple)) and len(w)==2
            lo,hi=w
            assert type(lo) is int and type(hi) is int
            assert 0<=lo<=K and lo<=hi<=INF
            row.append((lo,hi))
        checked.append(tuple(row))
    lookup=lookup_function(sites)
    initial=tuple((v,v) for v in INITIAL)
    start=lookup('')
    assert checked[start] is not None,'initial site cannot be unreachable'
    assert join(checked[start],initial)==checked[start],'initial inclusion'
    edges=0
    for row,v in zip(sites,checked):
        if v is None:continue
        for p,w,case in transitions(row,v):
            j=lookup(p)
            assert checked[j] is not None,('successor marked unreachable',row,p)
            assert join(checked[j],w)==checked[j],('successor inclusion',row,p)
            edges+=1
    return checked,edges

def main():
    sites = program_sites()
    lookup=lookup_function(sites)
    initial = tuple((v,v) for v in INITIAL)
    vals = [None]*len(sites)
    start = lookup('')
    vals[start] = initial
    q = deque([start]); queued = {start}; updates = 0
    while q:
        i=q.popleft(); queued.remove(i)
        for p,v,case in transitions(sites[i], vals[i]):
            j=lookup(p)
            w=join(vals[j],v)
            if w != vals[j]:
                vals[j]=w; updates+=1
                if j not in queued: q.append(j);queued.add(j)
    # Independently validate local closure, rather than trusting worklist stop.
    vals,closure_edges=validate_invariants(sites,vals)
    c=Counter()
    cases=[]
    for i,(row,v) in enumerate(zip(sites,vals)):
        p,op,r=row
        if v is None:
            c['unreachable_sites']+=1
            continue
        c['reachable_sites']+=1
        if op=='CD':
            lo,hi=v[r]
            c['zero_cases']+=int(lo==0);c['positive_cases']+=int(hi>0)
            if lo>0 or hi==0: cases.append(dict(index=i,pc=p,register=r,value=list(v[r]),possible='positive' if lo>0 else 'zero'))
        else: c['other_cases']+=1
    c['guarded_cases']=c['zero_cases']+c['positive_cases']+c['other_cases']
    from hashlib import sha256
    out=dict(status='PASS',domain=dict(lower_cap=K,infinity_code=INF),initial=[list(x) for x in initial],
        source_sha256=sha256((BASE/'sources/Prog254.v').read_bytes()).hexdigest(),
        source_site_count=len(sites),closure_edges=closure_edges,
        counts=dict(c), updates=updates, forced_branches=cases,
        invariants=[None if v is None else [list(w) for w in v] for v in vals])
    dest=Path(__file__).resolve().parents[1]/'results/interval-invariants.json'
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(counts=dict(c),updates=updates,forced_branches=cases[:20]),indent=2))

if __name__=='__main__':
    assert __debug__,'Assertions are required; do not use -O.'
    main()
