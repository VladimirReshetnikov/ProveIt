#!/usr/bin/env python3
"""Plain set-tape simulator for the supplied binary one-tape machines.

A finite run does not establish non-halting. Initial state 0, all-zero tape,
head 0, halting state 194. No arithmetic shortcuts or bounded tape window.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def read(path):
    rows={}
    for line in path.read_text().splitlines():
        q,b,w,d,n=line.split()
        q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,b]=(w,1 if d=='R' else -1,n)
    assert set(rows)=={(q,b) for q in range(194) for b in (0,1)}
    assert all(0<=n<=194 for w,d,n in rows.values())
    return rows

def simulate(path,limit):
    rows=read(path)
    state,head,ones,steps=0,0,set(),0
    while steps<limit and state!=194:
        write,move,state=rows[state,int(head in ones)]
        (ones.add if write else ones.discard)(head)
        head+=move
        steps+=1
    return {'steps':steps,'state':state,'head':head,'halted':state==194,
            'one_cells':sorted(ones),'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family',choices=('GD','GDH','GDHS'),default='GD')
    p.add_argument('--steps',type=int,default=100000)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    assert a.steps>=0
    result=simulate(ROOT/'machines'/a.family/'machine.tm',a.steps)
    result['native_state']=json.loads((ROOT/'machines'/a.family/'labels.json').read_text())[result['state']]
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
