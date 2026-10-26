#!/usr/bin/env python3
"""Explore exact acyclic monic eliminations with literal degree budgets.

The resulting finite pivot lists require independent replay before publication.
No claim of optimality is made. Original quadratic rows are never modified.
"""
import argparse, json, math, random, time
from pathlib import Path
from collections import defaultdict
import audit_source_interface as A

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--source',type=Path,default=A.DEFAULT)
    ap.add_argument('--cap',type=int,required=True);ap.add_argument('--runs',type=int,default=12)
    ap.add_argument('--weighted',action='store_true');ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--partition',default='[[0,1,2,3,4]]')
    args=ap.parse_args(); source=json.loads(args.source.read_text());interface=A.audit(args.source)
    rows=[A.parse(r['terms']) for r in source['residuals']]
    partition=json.loads(args.partition)
    if sorted(j for g in partition for j in g)!=list(range(5)) or any(not g for g in partition):raise ValueError('partition')
    forbidden=set(interface['deleted_variables']);original_removed=set(interface['deleted_rows'])
    n=len(source['variables']); valid=set(range(n))-forbidden
    candidates=[]
    for j,row in enumerate(rows):
        if j in original_removed:continue
        occurrences=defaultdict(int)
        for mon,c in row.items():
            for v in set(mon):occurrences[v]+=1
        for (v,),c in [(m,c) for m,c in row.items() if len(m)==1 and abs(c)==1]:
            if v in valid and occurrences[v]==1:
                repl={m:-c*k for m,k in row.items() if m!=(v,)}
                candidates.append((j,v,repl))
    reqs={r['request']:r for r in interface['requests']};block_polys=[]
    for block in interface['blocks']:
        nn=A.parse(block['base']);H={};S={}
        for no in block['requests']:
            r=reqs[no];m=A.parse(r['m']);X=A.parse(r['X']);Y=A.parse(r['Y']);D=A.parse(r['D'])
            H=A.add(H,A.mul(Y,A.sub(m,X)));S=A.add(S,A.sub(A.sq(A.sub(m,D)),A.sq(Y)))
        E=A.sub(S,A.scale(2,A.mul(nn,H)))
        if args.weighted:E=A.mul(nn,E)
        block_polys.append((A.parse(block['T']),E))
    # Source152's published profiles are only search priorities, never proofs.
    pref={k:set(v) for k,v in json.loads((HERE.parent/'inputs/monic_priority_names.json').read_text()).items()}
    usage=[sum(any(v in m for m in row) for row in rows) for v in range(n)]
    def evaluate(defs, removed):
        degrees={v:1 for v in valid if v not in defs};visiting=set()
        def degree(v):
            if v in degrees:return degrees[v]
            if v in visiting:raise ValueError('cycle')
            visiting.add(v);poly=defs[v][1]
            d=max((sum(degree(k) for k in mon) for mon in poly),default=0)
            degrees[v]=d;visiting.remove(v);return d
        try:
            for v in valid:degree(v)
        except (ValueError,RecursionError):return None
        def pd(p):return max((sum(degrees[v] for v in m) for m in p),default=0)
        rds=[pd(row) for j,row in enumerate(rows) if j not in removed]
        td=[pd(t) for t,e in block_polys];ed=[pd(e) for t,e in block_polys]
        poolds=[]
        for group in partition:
            total=sum(td[j] for j in group)
            poolds.append(max([1+total]+[ed[j]+total-td[j] for j in group]))
        poold=max(poolds);md=max(rds+poolds)
        if md>args.cap:return None
        return {'degree_bound':2*md,'pool_residual_degree_bound':poold,
                'core_residual_degree_bounds':rds,'variable_degrees':degrees,'pool_residual_degree_bounds':poolds,
                'T_degrees':td,'numerator_degrees':ed,
                'cost':sum(d*d for d in rds)+poold*poold}
    all_results=[];best=None;t0=time.time()
    for seed in range(args.runs):
        rng=random.Random(172216+seed);defs={};removed=set(original_removed);steps=[]
        priority=list(pref)[seed%len(pref)]; noise={ (r,v):rng.random() for r,v,repl in candidates}
        while True:
            options=[]
            for r,v,repl in candidates:
                if r in removed or v in defs:continue
                test={**defs,v:(r,repl)};metric=evaluate(test,removed|{r})
                if metric is None:continue
                # Several deterministic objectives probe different DAG cuts.
                mode=seed%5;name=source['variables'][v]['name'];prefer=name in pref[priority]
                inc=metric['cost'];d=metric['variable_degrees'][v]
                if mode==0:score=(inc,d,len(repl),usage[v],noise[r,v])
                elif mode==1:score=(not prefer,inc+noise[r,v]*10,d,len(repl))
                elif mode==2:score=(d,usage[v],inc+noise[r,v]*40)
                elif mode==3:score=(inc+noise[r,v]*100,d,len(repl))
                else:score=(not prefer,d,len(repl),inc+noise[r,v]*80)
                options.append((score,r,v,repl,metric))
            if not options:break
            _,r,v,repl,metric=min(options,key=lambda z:z[0]);defs[v]=(r,repl);removed.add(r)
            steps.append({'row':r,'variable':v})
        metric=evaluate(defs,removed);metric.pop('cost')
        result={'source_sha256':interface['source_sha256'],'weighted':args.weighted,'seed':seed,'partition':partition,
                'max_residual_degree':args.cap,'steps':steps,'eliminated':len(defs),
                'variables':len(valid)+len(partition)-len(defs),'residuals':len(rows)-len(removed)+len(partition),
                **metric}
        result['variable_degrees']=[metric['variable_degrees'].get(i,None) for i in range(n)]
        all_results.append(result)
        if best is None or (result['variables'],result['degree_bound'])<(best['variables'],best['degree_bound']):
            best=result
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps({'best':best,'runs':all_results},sort_keys=True,indent=2)+'\n')
        print(json.dumps({'seed':seed,'variables':result['variables'],'degree_bound':result['degree_bound'],'elapsed':round(time.time()-t0,2)}),flush=True)
    args.output.write_text(json.dumps({'best':best,'runs':all_results},sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
