#!/usr/bin/env python3
"""Independent check of the dense labels and complete transition bijection."""
import argparse,hashlib,json
from pathlib import Path

def read(path):
    out={}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b)not in out and b in(0,1)and w in(0,1)and d in('L','R')
        out[q,b]=w,d,z
    return out

def audit(native,compact,recipe):
    a,b=read(native),read(compact);r=json.loads(Path(recipe).read_text())
    states=sorted({q for q,bit in a});assert len(states)==218 and states[0]==0
    m={q:i for i,q in enumerate(states)};m[254]=218
    assert m=={int(q):v for q,v in r['native_to_compact'].items()}
    assert b=={(m[q],bit):(w,d,m[z])for(q,bit),(w,d,z)in a.items()}
    assert set(b)=={(q,bit)for q in range(218)for bit in(0,1)}
    assert {z for w,d,z in b.values()}-set(range(218))=={218}
    assert hashlib.sha256(Path(native).read_bytes()).hexdigest()==r['output_sha256']
    assert hashlib.sha256(Path(compact).read_bytes()).hexdigest()==r['compact_sha256']
    return dict(verified=True,working_states=218,transition_rows=436,start=0,halt=218,
                compact_sha256=r['compact_sha256'],native_sha256=r['output_sha256'],
                statement='Every compact transition is the bijective image of its native transition.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('native');p.add_argument('compact');p.add_argument('recipe');a=p.parse_args()
    print(json.dumps(audit(a.native,a.compact,a.recipe),indent=2))
