"""Independently check every macro CFG edge under an explicit zero-unused-slot invariant.

Each symbolic value is an affine integer expression in the nine source values.
Guard singleton facts come only from the checked phase masks. No samples are used.
"""
from pathlib import Path
from collections import Counter
import json
import dynamic_renaming as d
import static_coalescing as c
ROOT=Path(__file__).parent
raw=json.loads((ROOT/'static-coalescing.json').read_text())
allocation={int(q):v for q,v in raw['allocation'].items()}
seen,edges,masks,variables,uf,adj,copies=c.graph()
ZERO=(0,)*10
def constant(k):return (k,)+(0,)*9
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def symbol(r):return (0,)+(0,)*r+(1,)+(0,)*(8-r)
def singleton(m):return m.bit_length()-1 if m and m&(m-1)==0 and m!=d.high else None

def input_values(site,kind):
    vals=[constant(k) if (k:=singleton(m)) is not None else symbol(r) for r,m in enumerate(masks[site])]
    if kind[0]=='step':
        _,_,op,r,z=d.cases[kind[1]]
        if op=='CD' and z:vals[r]=ZERO
        elif op=='CD':
            k=singleton(masks[site][r]&~1)
            if k is not None:vals[r]=constant(k)
    return vals

def encode(site,logical):
    colors=allocation[site]
    assert all(x is None or isinstance(x,int) and 0<=x<9 for x in colors)
    assert len([x for x in colors if x is not None])==len(set(x for x in colors if x is not None))
    tape=[ZERO]*9
    for r,color in enumerate(colors):
        if color is None:
            assert logical[r]==ZERO,('unallocated_nonzero',site,r,logical[r])
        else:tape[color]=logical[r]
    return tape

def choice(site,dst,kind):
    colors=allocation[site]
    if kind[0]=='move':
        r,t=kind[1:];a=colors[r];b=allocation[dst][t]
        return ('erase',) if a is None or b is None or a==b else ('move',a,b)
    _,_,op,r,z=d.cases[kind[1]]
    if op=='CI':
        color=colors[r] if colors[r] is not None else allocation[dst][r]
        assert color is not None
        return 'inc',color
    if op=='CD':
        color=colors[r]
        if color is None:color=min(set(range(9))-set(colors))
        return 'dec0' if z else 'decp',color
    return ('control',)

records=[];modes=Counter()
halt_sites=[]
for site,out in sorted(edges.items()):
    if not out:
        assert d.sites[site][1]=='CH',('unexplained_terminal',site,d.sites[site])
        halt_sites.append(site)
    for dst,kind in out:
        before=input_values(site,kind);wanted=before.copy();actual=encode(site,before)
        recipe=choice(site,dst,kind)
        if kind[0]=='move':
            r,t=kind[1:];assert before[t]==ZERO
            wanted[t]=add(wanted[t],wanted[r]);wanted[r]=ZERO
        else:
            _,_,op,r,z=d.cases[kind[1]]
            if op=='CI':wanted[r]=add(wanted[r],constant(1))
            elif op=='CD' and not z:wanted[r]=sub(wanted[r],constant(1))
        if recipe[0]=='inc':actual[recipe[1]]=add(actual[recipe[1]],constant(1))
        elif recipe[0]=='dec0':assert actual[recipe[1]]==ZERO
        elif recipe[0]=='decp':actual[recipe[1]]=sub(actual[recipe[1]],constant(1))
        elif recipe[0]=='move':
            _,a,b=recipe;assert a!=b and actual[b]==ZERO
            actual[b]=add(actual[b],actual[a]);actual[a]=ZERO
        expected=encode(dst,wanted)
        assert actual==expected,('edge_mismatch',site,dst,kind,recipe,actual,expected)
        modes[recipe[0]]+=1
        records.append(dict(source=site,target=dst,kind=kind,recipe=recipe))
assert encode(d.first,[ZERO]*9)==[ZERO]*9
# A decrement test is one physical primitive with two possible outcomes.
for site,out in edges.items():
    if len(out)==2:
        rec=[choice(site,dst,kind) for dst,kind in out]
        assert rec[0][0]=='dec0' and rec[1][0]=='decp' and rec[0][1]==rec[1][1]
assert len(halt_sites)==1
result=dict(status='PASS exact symbolic affine edge certificate',edges=len(records),sites=len(seen),modes=dict(modes),initial_zero_slots=True,all_unused_slots_zero_preserved=True,allocated_physical_slots=9,halt_sites=halt_sites,records=records)
(ROOT/'allocation-certificate.json').write_text(json.dumps(result))
print({k:v for k,v in result.items() if k!='records'})
