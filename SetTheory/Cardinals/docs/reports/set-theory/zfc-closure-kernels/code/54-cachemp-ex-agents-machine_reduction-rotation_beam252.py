#!/usr/bin/env python3
"""Deterministic beam search of coordinated closed decoder rotations.

Counts literal emitted table states. The graph bound is conservative and
accepted rotations still need the separate symbolic runtime and blank boot.
"""
import rotation_search252 as r
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse,hashlib,heapq,json,time

def tree_key(nodes,root):
    @lru_cache(None)
    def key(e):
        return ('N',key(nodes[e[1]][0]),key(nodes[e[1]][1])) if e[0]=='N' else e
    return hashlib.sha256(repr(key(('N',root))).encode()).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=480);ap.add_argument('--expansions',type=int,default=1000);ap.add_argument('--ceiling',type=int,default=257);ap.add_argument('--output',type=Path,default=r.HERE/'rotation-beam-results.json');ap.add_argument('--cache-mp',action='store_true');args=ap.parse_args()
    if args.cache_mp:
        r.OLD=json.loads((r.HERE/'mp-cache-decoder-entries.json').read_text());r.NODES={int(k):tuple(map(tuple,v)) for k,v in r.OLD['nodes'].items()};r.ROOT=r.OLD['root'];r.OLD_FP={v:int(k) for k,v in r.OLD['fingerprints'].items()};r.BASE=dict(r.BASE);r.BASE['204',1]=(1,'R','151');r.CONTROL_OPTIONS={}
        for n,pair in r.NODES.items():
            for bit,e in enumerate(pair):
                if e[0] not in 'BC':continue
                counts=r.CONTROL_OPTIONS.setdefault((e,bit),Counter())
                for state,weight in r.OLD['state_entries'][str(n)].items():counts[r.BASE[state,bit]]+=weight
        assert r.emit(r.NODES,r.ROOT)==r.BASE
    seen={tree_key(r.NODES,r.ROOT)};frontier=[(252,203,0,r.NODES,r.ROOT,[])];candidates=[];hist=Counter();serial=0;expanded=0;attempted=0;costed=0;first=time.monotonic();best=252;minimum_by_expansion=[]
    outdir=r.HERE/'rotation-candidates';outdir.mkdir(exist_ok=True)
    while frontier and expanded<args.expansions and time.monotonic()-first<args.seconds:
        priority,nodecount,_,nodes,root,path=heapq.heappop(frontier);expanded+=1
        for n,e,k in r.options(nodes):
            attempted+=1;ns,nr=r.mutate(nodes,root,n,e);m=r.metrics(ns,nr)
            if m[1]>7 or m[2]>39:hist['shape']+=1;continue
            key=tree_key(ns,nr)
            if key in seen:hist['repeat']+=1;continue
            seen.add(key)
            try:table=r.gc(r.emit(ns,nr))
            except KeyError:hist['unsupported_leaf']+=1;continue
            costed+=1;cost=len(table)//2;hist[str(cost)]+=1
            if cost>args.ceiling:continue
            serial+=1;history=path+[(n,k)]
            heapq.heappush(frontier,(cost,len(ns),serial,ns,nr,history))
            if cost<best:best=cost;print('NEW BEST',cost,'path',history,flush=True)
            if cost<=251:
                stem=f'beam-{"cache-" if args.cache_mp else ""}{serial}-{cost}';r.save(outdir/(stem+'.tm'),table);(outdir/(stem+'.json')).write_text(json.dumps({'nodes':ns,'root':nr,'path':history,'key':key},indent=2)+'\n');candidates.append(stem)
        minimum_by_expansion.append([expanded,priority,len(frontier),best])
        if expanded%10==0:print('Expanded',expanded,'frontier',len(frontier),'unique',len(seen),'best',best,'elapsed',round(time.monotonic()-first,2),flush=True)
    report={'source_commit':'43026ff42f0939f09b9e95495248cfadcad38e38','start_graph_states':252,'best_graph_states':best,'expansion_limit':args.expansions,'wall_seconds_limit':args.seconds,'retained_cost_ceiling':args.ceiling,'expanded':expanded,'attempted_rotations':attempted,'unique_dags_seen':len(seen),'tables_costed':costed,'remaining_frontier':len(frontier),'histogram':hist,'candidates':candidates,'elapsed_seconds':time.monotonic()-first,'expansion_ledger':minimum_by_expansion,'status':'frontier_exhausted' if not frontier else 'bound_reached','scope':'Source closed-region rotations; actual machine graph counts. No modified runtime or blank initialization is proved by this count.'}
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('expansion_ledger','histogram')},indent=2),flush=True)

if __name__=='__main__':main()
