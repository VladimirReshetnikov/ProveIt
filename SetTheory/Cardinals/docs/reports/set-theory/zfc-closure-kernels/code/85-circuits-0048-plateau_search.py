#!/usr/bin/env python3
"""Explore bounded closed-layout rotations with exact table-graph costs.

Graph reachability and exact state bisimulation are only cost gates. Every
interesting candidate must separately pass universal instruction contracts
and a whole-tape blank initializer before an endpoint can be claimed.
"""
import sys,json,time,random,argparse
from pathlib import Path
from collections import Counter,deque
import search246 as s
import rotate_search as r

def reach(T,start='95'):
    seen=set();todo=[start]
    while todo:
        q=todo.pop()
        if q in seen or q=='254':continue
        seen.add(q);todo.extend(T[q,b][2] for b in (0,1))
    return seen

def minimize(T,qs):
    qs=sorted(qs,key=int);part={q:0 for q in qs}
    while True:
        d={};p={q:d.setdefault(tuple((w,m,-1 if t=='254' else part[t]) for w,m,t in (T[q,0],T[q,1])),len(d))for q in qs}
        if p==part:return len(d)
        part=p

def metrics(N,root):
    T,_=s.emit(N,root);qs=reach(T);n=len(qs)
    return n,minimize(T,qs) if n<=249 else n

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--ceiling',type=int,default=247);ap.add_argument('--max-nodes',type=int,default=500);ap.add_argument('--output',type=Path,default=Path('plateau-replay'));a=ap.parse_args()
    t0=time.monotonic();out=a.output;out.mkdir(parents=True,exist_ok=True)
    queue=deque([(s.NODES,s.ROOT,[])]);seen={s.fingerprints(s.NODES)[s.ROOT]};hist=Counter();wins=[];expanded=0;proposals=0;best=246
    while queue and time.monotonic()-t0<a.seconds and expanded<a.max_nodes:
        N,root,path=queue.popleft();expanded+=1
        for index,(n,e,k) in enumerate(r.options(N)):
            proposals+=1;nn,nr=r.mutate(N,root,n,e);fp=s.fingerprints(nn)[nr]
            if fp in seen:continue
            seen.add(fp)
            z=r.zero_metrics(nn,nr)
            if z[1]>7 or z[2]>39:hist['shape']+=1;continue
            try:g,cost=metrics(nn,nr)
            except (KeyError,IndexError):hist['unsupported']+=1;continue
            hist[str(cost)]+=1
            newpath=path+[(n,index,k)]
            if cost<best:
                best=cost;name=f'candidate-{cost}-{proposals}'
                (out/(name+'.json')).write_text(json.dumps(dict(root=nr,nodes=nn,path=newpath,graph_states=g,quotient_states=cost),indent=2)+'\n')
                wins.append(name);print('NEW',name,'path',newpath,flush=True)
            if cost<=a.ceiling:queue.append((nn,nr,newpath))
        if expanded%10==0:print('expanded',expanded,'proposals',proposals,'queue',len(queue),'best',best,'seconds',round(time.monotonic()-t0,2),flush=True)
    result=dict(scope='Breadth-first closed rotations through table-graph cost plateau; no semantic or global minimality inference.',expanded=expanded,proposals=proposals,distinct_fingerprints=len(seen),queue_remaining=len(queue),best_graph_quotient=best,ceiling=a.ceiling,seconds=time.monotonic()-t0,histogram=hist,winners=wins,completed=not queue)
    (out/f'results-ceiling{a.ceiling}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
