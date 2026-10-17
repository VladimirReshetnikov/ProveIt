#!/usr/bin/env python3
"""Bounded joint decoder-reassociation search using literal graph size.

Every accepted graph-size improvement is still required to pass the complete
conditional affine checker and a whole-tape blank bootstrap before promotion.
"""
from pathlib import Path
import argparse, hashlib, json, math, random, time
import joint_rotation_search as s

def reachable(table):
    seen={'96','64'}|{q for q,b in s.BOX_PAIRS}
    todo=list(seen)
    while todo:
        q=todo.pop()
        for b in (0,1):
            t=table[q,b][2]
            if t!='254' and t not in seen:seen.add(t);todo.append(t)
    return seen

def count(nodes,root):
    z=s.rot.zero_metrics(nodes,root)
    if z[1]>7 or z[2]>39:return None,None
    try:table=s.emit(nodes,root)
    except KeyError:return None,None
    return len(reachable(table)),table

def main():
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=60);p.add_argument('--iterations',type=int,default=20000);p.add_argument('--seed',type=int,default=20261017);p.add_argument('--output',type=Path,default=Path(__file__).with_name('multi_rotation_results.json'));a=p.parse_args()
    assert __debug__
    begin=time.monotonic();rng=random.Random(a.seed);best=(s.NODES,s.ROOT_NODE);bestcost=252
    cur,root=best;cost=bestcost;recipe=[];best_recipe=[];accepted=0;done=0;records=[];proposals=[]
    outcome_counts={}
    for i in range(a.iterations):
        if time.monotonic()-begin>a.seconds:break
        if i%1000==0:cur,root=best;cost=bestcost;recipe=best_recipe.copy()
        options=s.rot.options(cur);j=rng.randrange(len(options));n,e,kind=options[j]
        nn,nr=s.rot.mutate(cur,root,n,e);nc,table=count(nn,nr);done+=1
        if nc is None:continue
        outcome_counts[nc]=outcome_counts.get(nc,0)+1
        temperature=.2+.9*(1-(i%1000)/1000)
        if nc<=cost or rng.random()<math.exp((cost-nc)/temperature):
            cur,root,cost=nn,nr,nc;recipe.append({'option_index':j,'node':n,'operation':kind});accepted+=1
        if cost<bestcost:
            best,bestcost,best_recipe=(cur,root),cost,recipe.copy()
            rec={'iteration':i,'graph_states':cost,'decoder_nodes':len(cur),'recipe':best_recipe.copy()}
            cert,used=s.certify(s.emit(cur,root),cur,root);rec['affine']=cert
            if cert['passed']:
                boot,bu=s.boot(s.emit(cur,root),1000000);rec['boot']=boot
                if boot['outcome']=='zero_root':
                    tm=s.prune(s.emit(cur,root),used|bu);rec['working_states']=len(tm)//2
                    out=a.output.with_suffix('.tm');out.write_text(s.text_table(tm));rec['table']=out.name;rec['table_sha256']=hashlib.sha256(out.read_bytes()).hexdigest()
            records.append(rec);print(json.dumps(rec),flush=True)
    out={'scope':'Bounded stochastic graph-size search over compositions of closed-block reassociations and commuting increments. Graph sizes are exact, conditional affine and blank endpoint results are explicitly separate.','seed':a.seed,'requested_iterations':a.iterations,'seconds_limit':a.seconds,'iterations':done,'accepted_mutations':accepted,'cost_histogram':outcome_counts,'best_graph_states':bestcost,'best_recipe':best_recipe,'improvements':records,'elapsed_seconds':time.monotonic()-begin}
    a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='cost_histogram'}),flush=True)

if __name__=='__main__':main()
