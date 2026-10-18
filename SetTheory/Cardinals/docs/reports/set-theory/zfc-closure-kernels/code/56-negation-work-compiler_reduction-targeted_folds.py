#!/usr/bin/env python3
"""Exhaustively screen specified deleted labels for a modified-source table.

Adapted from the parent experiment fold_modified_source.py. All incoming
references are redirected, and each retained row is chosen from either state.
Exact trace incidence filters cases; survivors receive an uncached full audit.
"""
from __future__ import annotations
import argparse,json,time
from collections import defaultdict,Counter
from pathlib import Path
import search_structural as s
import warm_rotation_search as w

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--reference',type=Path,default=s.HERE/'direct_negation/fresh.json')
    ap.add_argument('--fold-log',type=Path,action='append',default=[])
    ap.add_argument('--deletes',type=int,nargs='+',default=[255]);ap.add_argument('--all',action='store_true')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);begun=time.monotonic()
    ns,r,org=w.load_source(a.source);ref,rr,ro=w.load_source(a.reference);folds=w.load_folds(a.fold_log)
    numeric=w.apply_folds(w.aligned_emit(ns,r,org,ref,rr,ro)[0],folds)
    rt,used=s.check(numeric,ns,r);assert rt['passed'],rt
    bt,bu=s.boot(numeric,150000);assert bt['outcome']=='zero_root',bt
    numeric=s.prune(numeric,used|bu);table={(str(q),b):(x,m,str(t)) for(q,b),(x,m,t) in numeric.items()}
    cs=list(s.cases(ns,r));inverse=defaultdict(set);protected={q for q,b in s.audit.BOX_PAIRS}|{64,96}
    for i,(p,e,z,reg,target) in enumerate(cs):
        tr=s.Tracking(table);s.strict.run(tr,p,(reg,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
        for row in tr.used:inverse[row].add(i)
    states=sorted({q for q,b in numeric});deletes=a.deletes+([q for q in states if q not in a.deletes] if a.all else [])
    hits=Counter();records=[];survivors=[];checks=0
    print('BASELINE',len(states),'cases',len(cs),'deletes',len(deletes),flush=True)
    for dead in deletes:
        if dead in protected or dead not in states:continue
        for keep in states:
            if keep==dead:continue
            for mask in range(4):
                changes={row:(x,m,str(keep)) for row,(x,m,t) in table.items() if t==str(dead) and row[0]!=str(dead)}
                for b in range(2):
                    if mask>>b&1:
                        x,m,t=table[str(dead),b];changes[str(keep),b]=x,m,str(keep) if t==str(dead) else t
                if any(changes.get((str(q),b),table[str(q),b])!=table[str(q),b] for q,b in s.audit.BOX_PAIRS):continue
                changes={row:v for row,v in changes.items() if table.get(row)!=v}
                affected=set()
                for q,b in changes:affected|=inverse[int(q),b]
                mt=table|changes;del mt[str(dead),0];del mt[str(dead),1];failure=None
                for i in sorted(affected,key=lambda k:(-hits[k],k)):
                    p,e,z,reg,target=cs[i];checks+=1
                    try:s.strict.run(mt,p,(reg,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
                    except (AssertionError,KeyError):failure=i;hits[i]+=1;break
                records.append([dead,keep,mask,failure,len(affected)])
                if failure is None:
                    nt={(int(q),b):(x,m,int(t)) for(q,b),(x,m,t) in mt.items()}
                    rt,used=s.check(nt,ns,r);assert rt['passed'],rt
                    bt,bu=s.boot(nt,150000);sv=dict(deleted=dead,target=keep,mask=mask,runtime=rt,boot=bt)
                    survivors.append(sv);print('SURVIVOR',dead,keep,mask,bt['outcome'],flush=True)
                    if bt['outcome']=='zero_root':
                        pt=s.prune(nt,used|bu);sv['working_states']=len(pt)//2
                        result=dict(outcome='passed',working_states=len(pt)//2,runtime=rt,boot=bt,table=pt,folds=folds+[(dead,keep,mask)])
                        s.save_candidate(result,ns,r,org,f'candidate_{dead}_{keep}_{mask}_{len(pt)//2}',a.output)
        print('DELETED_LABEL_DONE',dead,len(records),checks,round(time.monotonic()-begun,1),flush=True)
        (a.output/'results.json').write_text(json.dumps(dict(source=str(a.source),input_states=len(states),folds=folds,
            recipes=records,survivors=survivors,checks=checks,elapsed=time.monotonic()-begun),indent=2)+'\n')
    print('DONE',len(survivors),len(records),checks,round(time.monotonic()-begun,1),flush=True)

if __name__=='__main__':main()
