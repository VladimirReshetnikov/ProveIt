#!/usr/bin/env python3
"""Erase two source loops whose entry register is certified zero.

Source-equivalence is conditional on the independently checked zero-root
invariant. Runtime checks are unconditional for the resulting source program.
This is an experiment, and makes no state-bound claim from source node count.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'compiler_reduction'))
import search_structural as s

PREFIXES=['11101001011000110','11111100']

def specialize(prefixes):
    new,seen,org={},{},defaultdict(set)
    def intern(a,b,origin):
        key=a,b
        if key not in seen:
            seen[key]=len(new);new[seen[key]]=key
        q=seen[key]
        org[q].add(origin)
        return 'N',q
    memo={}
    def unchanged(e):
        if e[0]!='N':return e
        if e[1] not in memo:
            a,b=s.NODES[e[1]]
            memo[e[1]]=intern(unchanged(a),unchanged(b),e[1])
        return memo[e[1]]
    def edge(e,path):
        if path in prefixes:
            assert e[0]=='N'
            assert s.NODES[e[1]][0][0]=='D'
            return 'B',0
        if not any(p.startswith(path) for p in prefixes):
            return unchanged(e)
        assert e[0]=='N'
        a,b=s.NODES[e[1]]
        return intern(edge(a,path+'0'),edge(b,path+'1'),e[1])
    root=edge(('N',s.ROOT),'')[1]
    return new,root,dict(org)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,default=HERE/'dead-loop-results')
    ap.add_argument('--allocation',default='origin')
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    for b in (0,1):s.CONTROL[('B',0),b][s.BASE[7,b]]=1
    results=[]
    for mask in [1,2,3]:
        prefixes=[p for i,p in enumerate(PREFIXES) if mask&(1<<i)]
        nodes,root,origins=specialize(prefixes)
        result=s.evaluate(nodes,root,origins,args.allocation,limit=1000000)
        table=result.pop('table',None)
        entry={'prefixes':prefixes,'nodes':nodes,'root':root,
               'origins':{q:sorted(v) for q,v in origins.items()},'result':result}
        (args.output/f'specialization{mask}.json').write_text(json.dumps(entry,indent=2)+'\n')
        if table is not None:
            (args.output/f'specialization{mask}.tm').write_bytes(s.audit.encode(table))
        results.append({k:v for k,v in result.items() if k not in ['emission','table']})
        print(mask,json.dumps(results[-1]),flush=True)
    (args.output/'summary.json').write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
