#!/usr/bin/env python3
"""Verify returned MILP feasible dictionaries, not their optimality claims."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
inc=('leaf','inc',1)
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
expected=tuple(tup(x) for x in json.loads((HERE.parent/'u2e4/word.json').read_text()))
for name in ['u2e4_free2.json','u2e4_free4.json']:
    d=json.loads((HERE/name).read_text());ps=d['productions'];seen=set()
    def expand(x,active=frozenset()):
        if isinstance(x,list):return (tuple(x),)
        if x=='node60':return (inc,)*2
        if x=='node61':
            assert 'free4' in name
            return (inc,)*4
        if x not in ps:return (x,)
        assert x not in active;seen.add(x)
        return sum((expand(y,active|{x}) for y in ps[x]),())
    got=expand(d['root'])
    assert got==expected and len(got)==193
    assert set(ps)==seen
    cost=sum(len(rhs)-1 for rhs in ps.values())
    assert cost==68 and abs(d['objective']-cost)<1e-6
    print(name,'PASS',len(ps),'reachable productions; exact cost',cost)
