#!/usr/bin/env python3
"""Compare exact affine physical clocks for all 61 successful constructor loops.

Substitutes the register/gap/spare updates between six source primitives.
Symbolic interpreter operation counts are deliberately not used as TM clocks.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'verification/vendor'))
from independent_runtime import inc

def inputs(path):
    return (json.loads((path/'sites.json').read_text()),
            json.loads((path/'instructions.json').read_text()),
            {(r['site'],r['positive']):r['duration'] for r in
             json.loads((path/'independent/contracts.json').read_text())})

def clock(sites,instructions,contracts,start):
    # Entry register7 = variable7 + 1, to describe precisely the positive branch.
    shift=[0]*13
    shift[2+7]=1
    total=[0]*13
    for index in range(start,start+6):
        address,op,arg=sites[index]
        positive=index==start
        duration=contracts[index,positive]
        offsets=shift.copy()
        if op=='dec' and positive:
            offsets[2+arg]-=1  # the case's variable is the predecessor value
        for j,v in enumerate(duration):
            total[j]+=v
        total[0]+=sum(duration[j]*offsets[j] for j in range(1,13))
        if op=='inc':
            shift[2+arg]+=1
            shift[12]+=3
            shift[1]+=inc(address)[1]
        elif op=='dec' and positive:
            shift[2+arg]-=1
            shift[1]+=1+inc(address)[1]
        else:
            assert op=='continueTo'
    assert instructions[start+5]==['jump',start]
    return total,shift

def main(out):
    assert __debug__
    base=inputs(ROOT/'reference/primary')
    sites,instructions,contracts=base
    starts=[]
    for k in range(len(instructions)-5):
        if (instructions[k]==['dec',7,k+6,k+1] and
            all(instructions[k+j]==['inc',1,k+j+1] for j in range(1,5)) and
            instructions[k+5]==['jump',k]):
            starts.append(k)
    assert len(starts)==61
    result=[]
    for name,expected in [('PA194LC',6),('PA194LC_A',18),('PA194LC_B',22),('PA194LC_C',18)]:
        directory=ROOT/'machines'/name
        other=inputs(directory)
        assert other[1]==instructions
        for start in starts:
            a,sa=clock(*base,start)
            b,sb=clock(*other,start)
            assert sa==sb
            assert [y-x for x,y in zip(a,b)]==[expected]+[0]*12
        result.append(dict(name=name,successful_loop_occurrences=61,
            extra_physical_transitions_per_iteration=expected,
            dense_sha256=hashlib.sha256((directory/'machine.tm').read_bytes()).hexdigest()))
    value=dict(status='PASS',scope='Matched input frames and exact affine physical clocks, not symbolic operation counts.',results=result)
    out.write_text(json.dumps(value,indent=2)+'\n')
    print(json.dumps(value,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=ROOT/'verification/iteration_cost.json')
    main(parser.parse_args().out)
