#!/usr/bin/env python3
"""Joint decoder-shape and return-counter cost experiment.

The current hardware scans nine zero cells to recognize return. Reducing every
decoder zero run from seven to six suggests deleting one counter state. We
score both literal decoder graph cost and the number of remaining zero-seven
leaf paths. Actual counter deletion still requires a full symbolic check.
"""
from functools import lru_cache
from pathlib import Path
import argparse,hashlib,json,math,random,time
import rotation_search252 as r

def seven_paths(nodes,root):
    @lru_cache(None)
    def f(e,z,hit):
        if e[0]!='N':return int(hit)
        a,b=nodes[e[1]]
        return f(a,z+1,hit or z+1>=7)+f(b,0,hit)
    return f(('N',root),0,False)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=12000);ap.add_argument('--seed',type=int,default=1729);ap.add_argument('--output',type=Path,default=r.HERE/'zero-run-search-results.json');args=ap.parse_args()
    rng=random.Random(args.seed);pareto={};candidates=[];history=[];count=0;first=time.monotonic();folder=r.HERE/'rotation-candidates'
    for weight in (.2,.5,1.0,2.0):
        nodes,root=r.NODES,r.ROOT;graph=252;bad=seven_paths(nodes,root);score=graph+weight*bad
        for i in range(args.iterations):
            n,e,k=rng.choice(r.options(nodes));ns,nr=r.mutate(nodes,root,n,e);m=r.metrics(ns,nr);count+=1
            if m[1]>7 or m[2]>39:continue
            try:t=r.gc(r.emit(ns,nr))
            except KeyError:continue
            ng=len(t)//2
            if ng>270:continue
            nb=seven_paths(ns,nr);nscore=ng+weight*nb;temp=.1+1.5*(1-i/args.iterations)
            if nscore<=score or rng.random()<math.exp((score-nscore)/temp):nodes,root,graph,bad,score=ns,nr,ng,nb,nscore
            if nb not in pareto or ng<pareto[nb]['graph_states']:
                stem=f'zero-run-{nb}-{ng}'
                pareto[nb]={'graph_states':ng,'seven_zero_paths':nb,'iteration':i,'weight':weight,'dag':stem+'.json','table':stem+'.tm'}
                (folder/(stem+'.json')).write_text(json.dumps({'nodes':ns,'root':nr,'metrics':m,'seven_zero_paths':nb},indent=2)+'\n');r.save(folder/(stem+'.tm'),t)
                print('FRONTIER',nb,ng,'weight',weight,'iteration',i,flush=True)
            effective=ng-1 if m[1]<=6 else ng
            if effective<252:
                stem=f'zero-counter-candidate-{len(candidates)}';short={(q,b):(w,d,'84' if target=='74' else target) for(q,b),(w,d,target)in t.items() if q!='74'}
                r.save(folder/(stem+'.tm'),short);(folder/(stem+'.json')).write_text(json.dumps({'nodes':ns,'root':nr,'deleted_counter_state':74,'replacement_counter_state':84}));candidates.append(stem);print('CANDIDATE',stem,'states',len(short)//2,flush=True)
            if i%2000==0:print('Progress',weight,i,graph,bad,round(time.monotonic()-first,2),flush=True)
    result={'seed':args.seed,'iterations_per_weight':args.iterations,'weights':[.2,.5,1.0,2.0],'attempts':count,'pareto_by_seven_zero_path_count':pareto,'counter_candidates':candidates,'elapsed_seconds':time.monotonic()-first,'scope':'Closed source rotations; graph-cost and zero-run diagnostics. Shorter return-counter hypothesis is unproved until complete altered-table execution checks.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
