#!/usr/bin/env python3
"""Closed-source rotation search after the exact direct-negation rewrite."""
from pathlib import Path
import argparse,json,random,math,time
import search_structural as s

HERE=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'direct_negation/hashcons.json');ap.add_argument('--output',type=Path,default=HERE/'negation_minimize');ap.add_argument('--iterations',type=int,default=200000);ap.add_argument('--seed',type=int,default=82552);ap.add_argument('--check',action='store_true')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);d=json.loads(a.input.read_text());nn={int(q):tuple(map(tuple,v)) for q,v in d['nodes'].items()};r=d['root'];oo={int(q):set(v) for q,v in d['origins'].items()}
    best=nn,r,oo;cost=len(nn);rng=random.Random(a.seed);history=[];t=time.monotonic();results=[]
    for i in range(a.iterations):
        if i and i%5000==0:nn,r,oo=best;history=[]
        n,e,kind=rng.choice(s.rotate.options(nn));cn,cr,co=s.mutate(nn,r,n,e,oo);m=s.rotate.zero_metrics(cn,cr)
        if m[1]>7 or m[2]>39:continue
        temp=.01+.22*(1-(i%5000)/5000)
        if len(cn)<=len(nn) or rng.random()<math.exp((len(nn)-len(cn))/temp):nn,r,oo=cn,cr,co;history.append([n,e,kind])
        if len(nn)<cost:
            cost=len(nn);best=nn,r,oo
            name=f'best_{i}_{cost}'
            (a.output/(name+'.json')).write_text(json.dumps(dict(nodes=nn,root=r,origins={q:sorted(v) for q,v in oo.items()},history=history),indent=2)+'\n')
            print('BEST',i,cost,'seconds',round(time.monotonic()-t,1),flush=True)
            if a.check:
                rr=s.evaluate(nn,r,oo,'fresh',150000);print('CHECK',rr['outcome'],rr.get('working_states'),rr.get('runtime'),flush=True)
                s.save_candidate(rr,nn,r,oo,name+'_machine',a.output)
            results.append([i,cost,time.monotonic()-t])
        if i%10000==0:print('SEARCH',i,'current',len(nn),'best',cost,'seconds',round(time.monotonic()-t,1),flush=True)
    (a.output/'summary.json').write_text(json.dumps(dict(best_nodes=cost,iterations=a.iterations,seed=a.seed,improvements=results,elapsed_seconds=time.monotonic()-t),indent=2)+'\n')
if __name__=='__main__':main()
