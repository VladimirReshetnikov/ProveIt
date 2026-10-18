#!/usr/bin/env python3
"""Delete one single-incoming state, synthesizing its predecessor's full action."""
from __future__ import annotations
import argparse,json,time
from collections import defaultdict,Counter
from pathlib import Path
import search_structural as s
import warm_rotation_search as w

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--reference',type=Path,default=s.HERE/'direct_negation/fresh.json')
    ap.add_argument('--fold-log',type=Path,action='append',default=[]);ap.add_argument('--deleted',type=int,default=255)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);begun=time.monotonic()
    ns,r,org=w.load_source(a.source);ref,rr,ro=w.load_source(a.reference);folds=w.load_folds(a.fold_log)
    numeric=w.apply_folds(w.aligned_emit(ns,r,org,ref,rr,ro)[0],folds)
    rt,used=s.check(numeric,ns,r);assert rt['passed'],rt
    bt,bu=s.boot(numeric,150000);assert bt['outcome']=='zero_root',bt
    numeric=s.prune(numeric,used|bu);dead=a.deleted
    incoming=[row for row,action in numeric.items() if action[2]==dead and row[0]!=dead]
    assert len(incoming)==1,incoming
    row=incoming[0];assert row not in s.audit.BOX_PAIRS
    table={(str(q),b):(x,m,str(t)) for(q,b),(x,m,t) in numeric.items()};cs=list(s.cases(ns,r))
    affected=[]
    for i,(p,e,z,reg,target) in enumerate(cs):
        tr=s.Tracking(table);s.strict.run(tr,p,(reg,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
        if row in tr.used:affected.append(i)
    states=sorted(({q for q,b in numeric}|{254})-{dead});records=[];survivors=[];hits=Counter();checks=0
    print('BASELINE',len(numeric)//2,'deleted',dead,'incoming',row,'affected',len(affected),flush=True)
    for targetstate in states:
        for write in range(2):
            for move in ['L','R']:
                mt=table.copy();del mt[str(dead),0];del mt[str(dead),1]
                mt[str(row[0]),row[1]]=write,move,str(targetstate);failure=None
                for i in sorted(affected,key=lambda k:(-hits[k],k)):
                    p,e,z,reg,target=cs[i];checks+=1
                    try:s.strict.run(mt,p,(reg,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
                    except (AssertionError,KeyError):failure=i;hits[i]+=1;break
                records.append([write,move,targetstate,failure])
                if failure is None:
                    nt={(int(q),b):(x,m,int(t)) for(q,b),(x,m,t) in mt.items()}
                    rt,used=s.check(nt,ns,r);assert rt['passed'],rt
                    bt,bu=s.boot(nt,150000);sv=dict(deleted=dead,incoming=row,action=[write,move,targetstate],runtime=rt,boot=bt)
                    survivors.append(sv);print('SURVIVOR',sv,flush=True)
                    if bt['outcome']=='zero_root':
                        pt=s.prune(nt,used|bu);sv['working_states']=len(pt)//2
                        result=dict(outcome='passed',working_states=len(pt)//2,runtime=rt,boot=bt,table=pt,
                            prior_folds=folds,deleted=dead,incoming=row,action=[write,move,targetstate])
                        s.save_candidate(result,ns,r,org,f'candidate_{targetstate}_{write}{move}_{len(pt)//2}',a.output)
    (a.output/'results.json').write_text(json.dumps(dict(source=str(a.source),input_states=len(numeric)//2,
        folds=folds,deleted=dead,incoming=row,affected_cases=len(affected),records=records,survivors=survivors,
        checks=checks,elapsed=time.monotonic()-begun),indent=2)+'\n')
    print('DONE',len(records),len(survivors),checks,round(time.monotonic()-begun,1),flush=True)

if __name__=='__main__':main()
