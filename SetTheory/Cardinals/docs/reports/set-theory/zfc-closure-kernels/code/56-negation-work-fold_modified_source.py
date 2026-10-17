#!/usr/bin/env python3
"""Local row fold search for a specified verified modified-source table.

Baseline trace incidence soundly avoids replaying cases whose read rows did not
change. Every survivor receives the complete suite and a literal blank boot.
No claim of semantic minimality is implied by an exhausted finite family.
"""
from __future__ import annotations
import argparse,json,sys,time
from collections import defaultdict,Counter
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'compiler_reduction'))
import search_structural as s

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,default=Path('work/negation-folds'));ap.add_argument('--all-states',action='store_true');a=ap.parse_args();a.output.mkdir(exist_ok=True,parents=True)
    d=json.loads(a.source.read_text());nodes={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root'];numeric=s.audit.read_table(a.table.read_bytes());cs=list(s.cases(nodes,root));begun=time.monotonic();allrounds=[]
    for iteration in range(20):
        table={(str(q),b):(w,m,str(t)) for (q,b),(w,m,t) in numeric.items()};states=sorted({q for q,b in numeric});inverse=defaultdict(set)
        for i,(p,e,z,r,target) in enumerate(cs):
            tr=s.Tracking(table);s.strict.run(tr,p,(r,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
            for row in tr.used:inverse[row].add(i)
        protected={q for q,b in s.audit.BOX_PAIRS}|{64,96};incoming=defaultdict(set)
        for row,(w,m,t) in numeric.items():incoming[t].add(row)
        deletes=[q for q in states if q not in protected and (q>=255 or a.all_states)]
        recipes=[];survivors=[];hits=Counter();checks=0;adopted=False
        print('ROUND',iteration,'states',len(states),'delete',len(deletes),'cases',len(cs),flush=True)
        for dead in deletes:
            for keep in states:
                if keep==dead:continue
                for mask in range(4):
                    changes={row:(w,m,str(keep)) for row,(w,m,t) in table.items() if t==str(dead) and row[0]!=str(dead)}
                    for b in range(2):
                        if mask>>b&1:
                            w,m,t=table[str(dead),b];changes[str(keep),b]=w,m,str(keep) if t==str(dead) else t
                    if any(row in changes and changes[row]!=table.get(row) for q,b in s.audit.BOX_PAIRS for row in [(str(q),b)]):continue
                    changes={row:v for row,v in changes.items() if table.get(row)!=v}
                    affected=set()
                    for q,b in changes:affected|=inverse[int(q),b]
                    testorder=sorted(affected,key=lambda i:(-hits[i],i))
                    mutant=table|changes
                    del mutant[str(dead),0];del mutant[str(dead),1]
                    failure=None
                    for i in testorder:
                        p,e,z,r,target=cs[i];checks+=1
                        try:s.strict.run(mutant,p,(r,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
                        except (AssertionError,KeyError):failure=i;hits[i]+=1;break
                    rec=[dead,keep,mask,failure,len(affected)];recipes.append(rec)
                    if failure is None:
                        mt={(int(q),b):(w,m,int(t)) for (q,b),(w,m,t) in mutant.items()}
                        rt,used=s.check(mt,nodes,root);assert rt['passed'],rt
                        boot,bu=s.boot(mt,1000000)
                        survivor=dict(deleted=dead,target=keep,mask=mask,runtime=rt,boot=boot)
                        survivors.append(survivor);print('RUNTIME SURVIVOR',dead,keep,mask,boot['outcome'],flush=True)
                        if boot['outcome']=='zero_root':
                            numeric=s.prune(mt,used|bu);adopted=True
                            (a.output/f'machine_{len(numeric)//2}.tm').write_bytes(s.audit.encode(numeric))
                            break
                if adopted:break
            if adopted:break
            if len(recipes)%1000<100:print('SEARCH',len(recipes),checks,'sec',round(time.monotonic()-begun,1),flush=True)
        rr=dict(iteration=iteration,input_states=len(states),recipes=len(recipes),checks=checks,records=recipes,survivors=survivors,adopted=adopted)
        allrounds.append(rr);out=dict(source=str(a.source),input_table=str(a.table),scope='Delete a nonprotected state; redirect all incoming targets to one survivor, choosing each survivor row from either original state; exact trace incidence filtering; Box contracts unchanged.',rounds=allrounds,final_states=len(numeric)//2,elapsed_seconds=time.monotonic()-begun)
        (a.output/'results.json').write_text(json.dumps(out,indent=2)+'\n')
        if not adopted:break
    print('DONE',len(numeric)//2,'sec',round(time.monotonic()-begun,1),flush=True)
if __name__=='__main__':main()
