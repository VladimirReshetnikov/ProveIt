#!/usr/bin/env python3
"""Exact finite combinatorial allocation using rational frequencies.

The theorem guarantees exhaustion when the count envelope and parameter conditions
hold. For arbitrary input this routine reports any residual, not a false success.
The rational demonstration uses small parameters to exercise actual phase/colour
classes, rather than claim those parameters satisfy the asymptotic theorem.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import json


def allocate(frequencies, h0, D, J, phase_counts=None):
    fs=[Fraction(x) for x in frequencies]
    if any(x<=0 for x in fs) or min(h0,D,J)<1:
        raise ValueError('expected positive frequencies and positive integer parameters')
    phase_counts=phase_counts or [100*j*j for j in range(1,J+1)]
    if len(phase_counts)!=J or min(phase_counts)<1:
        raise ValueError('need a positive phase count for each level')
    R1=(phase_counts[0]+1)*phase_counts[0]*h0
    base=[(i,x) for i,x in enumerate(fs) if x<R1]
    residual=[(i,x) for i,x in enumerate(fs) if x>=R1]
    layers=[]
    for j,M in enumerate(phase_counts,1):
        h=h0*2**(j-1); cap=D*h; R=(M+1)*M*h
        bins=defaultdict(list); unassigned=[]
        for tag,x in residual:
            k=int(x//h)
            if k*h<R: unassigned.append((tag,x))
            else: bins[k].append((tag,x))
        groups=defaultdict(list)
        for k,items in sorted(bins.items()):
            items.sort(key=lambda t:(t[1],t[0]))
            cell,phase=divmod(k,M)
            assert cell>=M+1
            for color,item in enumerate(items[:cap]):
                groups[phase,color].append(item)
            unassigned.extend(items[cap:])
        # Verify each class contains at most one occurrence per eligible phase bin.
        for (phase,color),items in groups.items():
            cells=[]
            for tag,x in items:
                cell,r=divmod(int(x//h),M)
                assert cell>=M+1 and r==phase and 0<=color<cap
                cells.append(cell)
            assert len(cells)==len(set(cells))
        assert len(groups)<=M*cap
        layers.append(groups); residual=unassigned
    alltags=[i for i,x in base]+[i for g in layers for items in g.values() for i,x in items]+[i for i,x in residual]
    assert sorted(alltags)==list(range(len(fs)))
    return base,layers,residual

if __name__=='__main__':
    fs=[Fraction(3,2),Fraction(3,2)]+[Fraction(65,2)]*7+[Fraction(67,2)]*3+[Fraction(131,2)]*9
    base,layers,residual=allocate(fs,h0=2,D=1,J=3,phase_counts=[2,2,2])
    def show(items): return [dict(tag=t,frequency=str(x)) for t,x in items]
    result=dict(description='Exact rational demo with small illustrative parameters; not a theorem-envelope test.',
                input_count=len(fs),base=show(base),
                layers=[dict(level=j,groups=[dict(phase=p,color=c,items=show(items)) for (p,c),items in sorted(g.items())]) for j,g in enumerate(layers,1)],
                residual=show(residual))
    # This example deliberately exhibits both carry and eligibility cutoffs.
    assert len(base)==2 and len(layers[0])>0 and len(layers[1])>0 and len(layers[2])>0
    Path(__file__).with_name('allocation_example.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Exact rational allocation example: all tags accounted for;',len(residual),'residual')
