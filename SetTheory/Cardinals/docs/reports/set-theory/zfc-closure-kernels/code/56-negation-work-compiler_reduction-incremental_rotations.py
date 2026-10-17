#!/usr/bin/env python3
"""Runtime-constrained source-rotation walk with exact trace reuse.

An unchanged case is reused only when its source instruction and guard agree
and no transition read by its previous successful symbolic run has changed.
This is the deterministic-trace preservation lemma, not a statistical screen.
Every saved improvement is also replayed by the complete uncached checker.
"""
from __future__ import annotations
import argparse, hashlib, json, math, random, time
from collections import Counter
from pathlib import Path
import search_structural as s
import warm_rotation_search as w

def incremental_check(table,nodes,root,parent_table=None,parent_cache=None):
    parent_table=parent_table or {};parent_cache=parent_cache or {}
    changes={row for row in table.keys()|parent_table.keys() if table.get(row)!=parent_table.get(row)}
    traced=s.Tracking({(str(q),b):(x,m,str(t)) for (q,b),(x,m,t) in table.items()})
    cache={};used=set();replayed=0;reused=0;count=0
    for p,e,z,r,target in s.cases(nodes,root):
        key=(p,e,z);previous=parent_cache.get(key)
        if previous is not None and previous.isdisjoint(changes):
            rows=previous;reused+=1
        else:
            traced.used=set()
            try:s.strict.run(traced,p,(r,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
            except (AssertionError,KeyError) as ex:
                return dict(passed=False,cases_passed=count,replayed=replayed,reused=reused,
                    failure=dict(path=p,operation=e,zero=z,reason=str(ex))),None,None,changes
            rows=traced.used;replayed+=1
        cache[key]=rows;used|=rows;count+=1
    return dict(passed=True,cases_passed=count,replayed=replayed,reused=reused),cache,used,changes

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--reference',type=Path,default=s.HERE/'direct_negation/fresh.json')
    ap.add_argument('--fold-log',type=Path,action='append',default=[])
    ap.add_argument('--iterations',type=int,default=10000);ap.add_argument('--seed',type=int,default=252)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);begun=time.monotonic();rng=random.Random(a.seed)
    folds=w.load_folds(a.fold_log);ref,rr,ro=w.load_source(a.reference)
    nn,nr,no=w.load_source(a.source)
    def emit(ns,r,org):return w.apply_folds(w.aligned_emit(ns,r,org,ref,rr,ro,stable_extra_labels=True)[0],folds)
    tab=emit(nn,nr,no);rt,cache,used,_=incremental_check(tab,nn,nr)
    assert rt['passed'],rt
    bt,bu=s.boot(tab,150000);assert bt['outcome']=='zero_root',bt
    count=len(s.prune(tab,used|bu))//2
    best=(count,nn,nr,no,tab,cache,bt,bu,used);counts=Counter();records=[];accepted=0;tested=set();bestcount=count
    print('BASELINE',count,'cases',rt['cases_passed'],'folds',folds,flush=True)
    for i in range(a.iterations):
        if i and i%500==0:
            count,nn,nr,no,tab,cache,bt,bu,used=best
        n,exp,kind=rng.choice(s.rotate.options(nn));cn,cr,co=s.mutate(nn,nr,n,exp,no)
        zm=s.rotate.zero_metrics(cn,cr)
        if zm[1]>7 or zm[2]>39:counts['shape']+=1;continue
        ct=emit(cn,cr,co)
        key=hashlib.sha256(s.audit.encode(ct)+s.fingerprints(cn)[cr].encode()).digest()
        if key in tested:counts['duplicate']+=1;continue
        tested.add(key)
        rt,cc,cu,changes=incremental_check(ct,cn,cr,tab,cache)
        counts['contracts_reused']+=rt['reused'];counts['contracts_replayed']+=rt['replayed']
        if not rt['passed']:
            counts['runtime_fail']+=1;continue
        if bu.isdisjoint(changes):cbt,cbu=bt,bu;counts['boot_reused']+=1
        else:cbt,cbu=s.boot(ct,150000)
        if cbt['outcome']!='zero_root':counts['boot_fail']+=1;continue
        pt=s.prune(ct,cu|cbu);cost=len(pt)//2;counts['passed']+=1
        record=dict(iteration=i,states=cost,source_nodes=len(cn),zero_metrics=zm,mutation=[n,exp,kind],
                    replayed=rt['replayed'],reused=rt['reused'])
        temperature=.2+.5*(1-(i%500)/500)
        accept=cost<=count or (cost<=bestcount+2 and rng.random()<math.exp((count-cost)/temperature))
        if accept:
            nn,nr,no,tab,cache,bt,bu,used=cn,cr,co,ct,cc,cbt,cbu,cu;count=cost;accepted+=1
            record['accepted']=True
        if cost<bestcount:
            full,fullused=s.check(pt,cn,cr);assert full['passed'],full
            fullbt,fullbu=s.boot(pt,150000);assert fullbt==cbt,(fullbt,cbt)
            bestcount=cost;best=(cost,cn,cr,co,ct,cc,cbt,cbu,cu)
            result=dict(outcome='passed',working_states=cost,runtime=full,boot=cbt,table=pt,
                        folds=folds,zero_metrics=zm,mutation=[n,exp,kind],iteration=i)
            s.save_candidate(result,cn,cr,co,f'best_{i}_{cost}',a.output)
            print('BEST',i,cost,'nodes',len(cn),'zero',zm,'sec',round(time.monotonic()-begun,1),flush=True)
        if accept or i%50==0:records.append(record)
        if i%50==0:
            print('PROGRESS',i,'current',count,'best',bestcount,'accepted',accepted,dict(counts),
                  'sec',round(time.monotonic()-begun,1),flush=True)
            (a.output/'results.json').write_text(json.dumps(dict(source=str(a.source),folds=folds,
                iterations=i+1,best_states=bestcount,accepted=accepted,counts=counts,records=records,
                elapsed=time.monotonic()-begun),indent=2)+'\n')
    (a.output/'results.json').write_text(json.dumps(dict(source=str(a.source),folds=folds,
        iterations=a.iterations,best_states=bestcount,accepted=accepted,counts=counts,records=records,
        elapsed=time.monotonic()-begun),indent=2)+'\n')
    print('DONE',bestcount,accepted,dict(counts),round(time.monotonic()-begun,1),flush=True)

if __name__=='__main__':main()
