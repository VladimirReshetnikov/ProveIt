"""Finite abstract interpretation over {zero, positive residues modulo 4}.

An invariant is verified independently as a post-fixed point after generation.
Bit 0 denotes exact zero, and bit 1+r denotes positive values congruent to r.
"""
import json,sys
from pathlib import Path
from collections import deque,Counter
M=4

def inc(mask):
    out=4 if mask&1 else 0
    for r in range(M):
        if mask&(1<<(r+1)):out|=1<<((r+1)%M+1)
    return out

def dec_positive(mask):
    out=0
    for r in range(M):
        if mask&(1<<(r+1)):
            out|=1<<((r-1)%M+1)
            if r==1:out|=1
    return out

def successors(row,values):
    values=list(values);op=row[0]
    if op=='halt':return []
    if op=='jump':return [(row[1],values)]
    if op=='inc':
        values[row[1]]=inc(values[row[1]])
        return [(row[2],values)]
    assert op=='dec'
    reg,zero,positive=row[1:];out=[]
    if values[reg]&1:
        v=values.copy();v[reg]=1;out.append((zero,v))
    if values[reg]&~1:
        v=values.copy();v[reg]=dec_positive(v[reg]);out.append((positive,v))
    return out

def derive(ins):
    inv=[None]*len(ins);inv[25]=tuple(8 if r==0 else 1 for r in range(9))
    todo=deque([25])
    while todo:
        pc=todo.popleft()
        for target,values in successors(ins[pc],inv[pc]):
            new=tuple(values) if inv[target]is None else tuple(a|b for a,b in zip(inv[target],values))
            if new!=inv[target]:inv[target]=new;todo.append(target)
    verify(ins,inv)
    return inv

def verify(ins,inv):
    assert len(ins)==len(inv)
    assert all(inv[25][r]&(8 if r==0 else 1) for r in range(9))
    for pc,row in enumerate(ins):
        if inv[pc]is None:continue
        assert len(inv[pc])==9 and all(0<x<32 for x in inv[pc])
        for target,values in successors(row,inv[pc]):
            assert inv[target]is not None
            assert all(v&~w==0 for v,w in zip(values,inv[target])),(pc,target)

if __name__=='__main__':
    ins=json.loads(Path(sys.argv[1]).read_text());inv=derive(ins)
    counts=Counter(v for row in inv if row is not None for v in row)
    Path(sys.argv[2]).write_text(json.dumps(inv)+'\n')
    print(json.dumps(dict(sites=len(ins),facts=dict(counts),nontrivial_congruence_facts=sum(n for x,n in counts.items()if x not in(1,30,31)),checked_postfixed_point=True),indent=2))
