"""Reproducible stochastic search of proven control-preserving reassociations.

Source-only discovery: no claim about binary state count follows from a hit.
The final source must be checked independently against the original graph.
"""
from pathlib import Path
import exact_reassociate as e
import random, math, json, time, argparse

p=argparse.ArgumentParser()
p.add_argument('--seconds',type=int,default=600)
p.add_argument('--seed',type=int,default=196237)
p.add_argument('--output',default='nonmonotone')
a=p.parse_args()
rng=random.Random(a.seed); began=time.monotonic()
root=e.ROOT; hist=[]; best=e.score(root); proposals=0; accepted=0; restarts=0
def cost(sc):
    return 3.0*(sc[0]-224)+1.5*max(sc[1]-6,0)+.03*(sc[2]-39)
cur=e.score(root); moved=0
while time.monotonic()-began<a.seconds:
    nodes=[n for n in e.live(root) if e.rotations(n)]
    n=rng.choice(nodes); alt,d,chunks,closed=rng.choice(e.rotations(n))
    nr=e.replace(root,n,alt); sc=e.score(nr); proposals+=1
    temperature=.5+.7*(1-(proposals%4000)/4000)
    if sc[0]<=227 and sc[1]<=7 and (cost(sc)<=cost(cur) or rng.random()<math.exp((cost(cur)-cost(sc))/temperature)):
        root=nr; cur=sc; accepted+=1; moved+=1
        hist.append(dict(node=n,alternative=alt,direction=d,chunks=chunks,all_closed=closed))
        if sc<best and sc[1]<=6:
            best=sc
            e.export(root,hist,a.output+'_best.json',dict(proposals=proposals,seed=a.seed))
            print('BEST',sc,'proposals',proposals,'accepted',accepted,'seconds',round(time.monotonic()-began,2),flush=True)
        if sc[0]<224 and sc[1]<=6:
            e.export(root,hist,a.output+'_found.json',dict(proposals=proposals,seed=a.seed))
            break
    if proposals%1000==0:
        root,hist=e.compact([(root,hist)])[0]
    if proposals%12000==0:
        root=e.ROOT; hist=[]; cur=e.score(root); restarts+=1
        e.compact([(root,hist)])
    if proposals%4000==0:
        print('PROGRESS',proposals,'cur',cur,'best',best,'sec',round(time.monotonic()-began,2),flush=True)
Path(a.output+'_receipt.json').write_text(json.dumps(dict(status='SOURCE_ONLY_HIT' if best[0]<224 else 'BOUNDED_SEARCH_NO_SMALLER_SOURCE',seed=a.seed,proposals=proposals,accepted=accepted,restarts=restarts,best=best,seconds=time.monotonic()-began,scope='Control-preserving rotations; up to227 DAG nodes and zero-run7 temporarily; final target223nodes and zero-run6. No binary state-count inference.'),indent=2)+'\n')
