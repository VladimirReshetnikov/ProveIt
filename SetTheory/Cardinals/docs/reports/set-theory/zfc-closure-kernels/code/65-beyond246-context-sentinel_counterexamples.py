#!/usr/bin/env python3
"""Literal false-sentinel witnesses for proposed 245/244 return scanners.

These reject the inherited universal instruction simulation. They do not prove
anything about the consistency strength of the altered machines' blank runs.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'baseline/zfc-context246'
sys.path.insert(0, str(BASE/'code'))
import check_literal_instructions as lit


def witness(states, last, removed):
    old=lit.read_table(BASE/'machine/zfc_prefix246_old.tm')
    table={key:row for key,row in old.items() if key[0] not in removed}
    table[last,0]=(0,-1,84)
    pc='111010010010000000'
    registers=[0]*9
    ones=lit.paint(pc,40,registers,[0],0)
    initial=sorted(ones)
    q,h=96,0
    events=[]
    for tick in range(2000):
        if q==96 and h==11:
            return dict(states=states,pc=pc,logical_instruction=['CD',1],
                physical_register=2,guard='zero',initial_head=0,initial_header=40,
                initial_registers=registers,initial_spares=[0],initial_ones=initial,
                false_dispatch_step=tick,false_dispatch_head=h,
                false_dispatch_ones=sorted(ones),events=events,
                conclusion='The shortened scanner mistakes an internal program-counter one at coordinate10 for the left marker; the inherited frame invariant fails.')
        b=int(h in ones)
        if q==last and b==0:
            events.append(dict(step=tick,state=q,head=h,
                local_origin=h-2,local_word=''.join(str(int(k in ones)) for k in range(h-2,h+11))))
        w,d,q=table[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    raise AssertionError('expected concrete witness was not reproduced')


def main():
    data=[witness(245,58,{74}),witness(244,41,{58,74})]
    assert data[0]['false_dispatch_step']==185
    assert data[1]['false_dispatch_step']==73
    path=ROOT/'sentinel-counterexamples.json'
    path.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':main()
