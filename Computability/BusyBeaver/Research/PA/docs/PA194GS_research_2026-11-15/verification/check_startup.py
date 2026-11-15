#!/usr/bin/env python3
"""Replay dense literal rows from an entirely zero, two-way infinite tape.

The sparse set stores all one cells. All unlisted cells are zero; no finite
window or external initial data is substituted for the actual blank tape.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]


def check(folder, output):
    assert __debug__
    rows={}
    for line in (folder/'machine.tm').read_text().splitlines():
        q,b,w,d,n=line.split()
        q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in rows and d in ('L','R')
        assert 0<=q<194 and b in (0,1) and w in (0,1) and 0<=n<=194
        rows[q,b]=(w,1 if d=='R' else -1,n)
    assert len(rows)==388
    labels=json.loads((folder/'labels.json').read_text())
    assert labels[0]==74 and labels[194]==254
    boundary=labels.index(84)
    ones=set()
    q=head=0
    for _ in range(57922):
        assert q!=194
        w,d,q=rows[q,int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head+=d
    assert (q,head)==(boundary,-2)
    path=json.loads((folder/'sites.json').read_text())[25][0]
    assert path=='1000000'
    registers=[0,0,0,0,0,0,2,0,0]
    frame=[1]+list(map(int,path))+[0]*(48-len(path))+[1]
    for value in registers+[1]*26:
        frame += [0]+[1]*(value+1)
    expected={head-1+i for i,b in enumerate(frame) if b==1}
    assert ones==expected
    result=dict(status='PASS',steps=57922,start=0,halt=194,
                dense_boundary=boundary,native_boundary=84,head=head,
                complete_one_support=sorted(ones),
                complete_tape_equality=True,initial_tape='all zero',
                dense_sha256=hashlib.sha256((folder/'machine.tm').read_bytes()).hexdigest())
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in
                     ('status','steps','head','complete_tape_equality','dense_sha256')}))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidate',type=Path,default=ROOT/'machine')
    p.add_argument('--output',type=Path,default=ROOT/'verification/startup.json')
    a=p.parse_args()
    check(a.candidate,a.output)
