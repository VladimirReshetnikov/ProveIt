#!/usr/bin/env python3
"""Check a finite inductive source invariant, without trusting its discovery."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
def transitions(row,values):
    op=row[0]
    if op=='halt': return []
    if op=='jump': return [(row[1],values)]
    reg=row[1]; d=values[reg]; out=[]; vs=list(values)
    if op=='inc':
        vs[reg]=(2 if d&1 else 0)|(4 if d&6 else 0)
        return [(row[2],tuple(vs))]
    assert op=='dec'
    if d&1:
        vs[reg]=1;out.append((row[2],tuple(vs)))
    if d&6:
        vs[reg]=(1 if d&2 else 0)|(6 if d&4 else 0)
        out.append((row[3],tuple(vs)))
    return out
def check():
    assert __debug__
    ins=json.loads((ROOT/'inputs/instructions.json').read_text())
    inv=json.loads((ROOT/'inputs/invariants.json').read_text())
    assert len(ins)==len(inv)==3776
    assert inv[25][0]&4 and all(v&1 for v in inv[25][1:])
    branches=0
    for i,v in enumerate(inv):
        if v is None: continue
        assert len(v)==9 and all(1<=d<=7 for d in v)
        for nxt,vals in transitions(ins[i],v):
            assert inv[nxt] is not None
            assert all((a|b)==b for a,b in zip(vals,inv[nxt]))
        branches += (int(bool(v[ins[i][1]]&1))+int(bool(v[ins[i][1]]&6))) if ins[i][0]=='dec' else 1
    assert branches==4875
    assert [i for i,v in enumerate(inv) if v is None]==[8]
    return {'inductive_closure_checked':True,'source_sites':3776,'reachable_sites':3775,'admissible_outcomes':branches,'abstract_domain':'bit1:{0}, bit2:{1}, bit4:{2,3,...}; independent registers'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
