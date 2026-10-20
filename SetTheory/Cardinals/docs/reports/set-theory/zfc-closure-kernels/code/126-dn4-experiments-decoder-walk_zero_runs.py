#!/usr/bin/env python3
"""Anneal open source reassociations toward a five-zero scanner bound.

This is candidate discovery: every emitted hit still needs a complete literal
runtime proof, including the shortened scanner when that optimization is used.
"""
from general_rotations import *
import math

ap=argparse.ArgumentParser()
ap.add_argument('--iterations',type=int,default=10000)
ap.add_argument('--seed',type=int,default=92738)
ap.add_argument('--output',type=Path,default=Path(__file__).parent/'zero_walk')
a=ap.parse_args();out=a.output;out.mkdir(exist_ok=True)
p=Path(__file__).parent/'dn4_open_rotations'
seeds=[]
def cost(t,lr):
    paths=c.sites(unlabel(lr));runs=sum('000000'in x[0]for x in paths)
    return runs+24*(len(t)//2-225),runs
for rec in json.loads((p/'representative_probes.json').read_text()):
    if rec['status']!='PASS_REPRESENTATIVE_CASES':continue
    name=rec['name'];t,_=v.parse_table((p/(name+'.tm')).read_bytes())
    r=c.tree(json.loads((p/(name+'_sites.json')).read_text()))
    seeds.append((t,labeled(t,r),name,[]))
q=Path(__file__).parent/'open_walk'
if(q/'best.tm').exists():
    t,_=v.parse_table((q/'best.tm').read_bytes());r=c.tree(json.loads((q/'best_sites.json').read_text()))
    seeds.append((t,labeled(t,r),'open_walk/best',[]))
rng=random.Random(a.seed);tt,lr,name,hist=rng.choice(seeds)
basegraph=c.graph_arithmetic(c.sites(unlabel(lr)));value,runs=cost(tt,lr)
seen=set();accepted=0;best=10000;tic=time.monotonic();stats=collections.Counter()
for step in range(a.iterations):
    if step%450==0:
        tt,lr,name,history=rng.choice(seeds);hist=history.copy();value,runs=cost(tt,lr)
    rs=moves(tt,lr,len(tt)//2<=226)
    if not rs:continue
    rot=rng.choice(rs);u,ur=perform(tt,lr,rot);key=tuple(sorted(u.items()))
    if key in seen:continue
    seen.add(key);r=unlabel(ur)
    try:
        if c.graph_arithmetic(c.sites(r))!=basegraph:stats['graph']+=1;continue
    except Exception:stats['invalid_graph']+=1;continue
    if bad_mapping(u,ur):stats['prefix']+=1;continue
    metrics=c.metrics(r)
    if metrics['maximum_zero_run']>6:stats['zero7']+=1;continue
    u,ur,rec=probe_folds(u,ur);n=len(u)//2
    if n>227:continue
    if u.get((38,0))!=(0,1,13):stats['known_helper_conflict']+=1;continue
    candidate,run=cost(u,ur);temp=3.0+(step%450)/150
    if candidate>value and rng.random()>math.exp((value-candidate)/temp):stats['anneal_reject']+=1;continue
    tt,lr=u,ur;value,runs=candidate,run
    hist.append(dict(rotation=rot,folds=rec['folds'],gc={k:z for k,z in rec['gc'].items()if k!='mapping'}));accepted+=1
    if value<best:
        best=value;print('BEST',step,n,runs,'value',value,'seed',name,'depth',len(hist),flush=True)
        label=f'best_{n}_{runs}'
        (out/(label+'.tm')).write_bytes(encode(tt));c.dump(out/(label+'_sites.json'),c.sites(unlabel(lr)))
        c.dump(out/(label+'_recipe.json'),dict(seed=name,history=hist))
        seeds.append((tt,lr,name,hist.copy()))
    if n<=224 or(n<=225 and runs==0):
        label=f'HIT_{a.seed}_{step}';(out/(label+'.tm')).write_bytes(encode(tt))
        c.dump(out/(label+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(label+'_recipe.json'),dict(seed=name,history=hist))
        print('HIT',step,n,runs,name,len(hist),flush=True);break
    if step%200==0:print('PROGRESS',step,'accepted',accepted,'n',n,'runs',runs,'secs',time.monotonic()-tic,flush=True)
else:
    result=dict(trials=a.iterations,accepted=accepted,distinct_trials=len(seen),stats=dict(stats),best_cost=best,seconds=time.monotonic()-tic)
    c.dump(out/'summary.json',result);print('DONE',json.dumps(result),flush=True)
