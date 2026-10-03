#!/usr/bin/env python3
"""Read-only verification of literal local rule exports and their global inverse."""
import hashlib,json,random
from collections import defaultdict
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def check():
    index=json.loads((ROOT/'examples/rule_index.json').read_text())
    rng=random.Random(20261002)
    cases=0
    for name,receipt in index.items():
        raw=(ROOT/'examples'/(name+'_rule.json')).read_bytes()
        assert hashlib.sha256(raw).hexdigest()==receipt['file_sha256']
        rule=json.loads(raw);v=rule['velocities'];s=rule['singleton_outputs'];n=len(v)
        assert len(s)==n==len(rule['types']) and sorted(s)==list(range(n))
        assert max(map(abs,v))==rule['radius']<=4
        pairs={tuple(r['input']):tuple(r['output']) for r in rule['pair_rows']}
        assert len(pairs)==len(rule['pair_rows']) and set(pairs)==set(pairs.values())
        assert all(len(a)==len(b)==2 and len(set(a))==len(set(b))==2 for a,b in pairs.items())
        invs={b:a for a,b in enumerate(s)};invp={b:a for a,b in pairs.items()}
        def onsite(conf,back=False):
            cells=defaultdict(list)
            for x,t in conf:cells[x].append(t)
            result=[]
            for x,tt in cells.items():
                tt=tuple(sorted(tt));assert len(tt)==len(set(tt))
                out=((invs[tt[0]],) if back else (s[tt[0]],)) if len(tt)==1 else (invp if back else pairs).get(tt,tt) if len(tt)==2 else tt
                result.extend((x,t) for t in out)
            return tuple(sorted(result))
        def forward(conf):return tuple(sorted((x+v[t],t) for x,t in onsite(conf)))
        def backward(conf):return onsite(tuple((x-v[t],t) for x,t in conf),True)
        for _ in range(500):
            conf=tuple(sorted(set((rng.randrange(-5,6),rng.randrange(n)) for _ in range(rng.randrange(1,9)))))
            assert backward(forward(conf))==forward(backward(conf))==conf
            assert len(forward(conf))==len(conf)
            cases+=1
    print(json.dumps({'status':'PASS','literal_rules':len(index),'random_inverse_cases':cases},indent=2))
if __name__=='__main__':check()
