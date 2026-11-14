#!/usr/bin/env python3
"""Recover tree reader entries from first visits to path positions."""
from collections import defaultdict
import symbolic as S
import json
from pathlib import Path

def node_map():
    root,defs=S.source_tree();sites=S.all_sites();m=S.load_machine()
    out=defaultdict(set)
    for path,op in sites:
        tape={i:b for i,b in enumerate(path)}
        tape[-1]=1;tape[48]=1
        q=S.ROOT;h=0;seen=set()
        for steps in range(1000):
            if 0<=h<=len(path) and h not in seen:
                t=root
                for b in path[:h]:
                    assert t[0]!='leaf'
                    t=t[b]
                out[t].add(q);seen.add(h)
                if h==len(path):break
            b=tape.get(h,0);w,d,q=m[q,b]
            tape[h]=w;h+=d
        else:raise ValueError(path)
    return out,defs

if __name__=='__main__':
    mapping,defs=node_map()
    named={name:sorted(mapping[t]) for name,t in defs.items()}
    print('internal',len({t for t in mapping if t[0]!='leaf'}),'mapped',len(mapping))
    print('multimaps',[(name,qs) for name,qs in named.items() if len(qs)!=1])
    print('leaves',[(t,sorted(qs)) for t,qs in mapping.items() if t[0]=='leaf'])
    Path(__file__).with_name('node_map.json').write_text(json.dumps(named,indent=2))
