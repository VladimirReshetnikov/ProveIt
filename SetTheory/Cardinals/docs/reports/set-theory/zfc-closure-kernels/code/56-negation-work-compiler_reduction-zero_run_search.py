#!/usr/bin/env python3
"""Joint source rebracketing and return-counter shortening experiment."""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
import argparse, hashlib, json, math, random, time
from pathlib import Path
import search_structural as s

HERE=Path(__file__).resolve().parent

def frozen_origins():
    bounds=s.rotate.edge_bounds(s.NODES)
    frozen=set()
    def freeze(n):
        if n in frozen:return
        frozen.add(n)
        for e in s.NODES[n]:
            if e[0]=='N':freeze(e[1])
    for n in s.NODES:
        if bounds(('N',n))[1:]==(0,0) and s.NODE_LABELS[n] not in s.PURE:
            freeze(n)
    # Retain the candidate enumerator and non-AX source region verbatim.
    ax=set()
    def visit(n):
        if n in ax:return
        ax.add(n)
        for e in s.NODES[n]:
            if e[0]=='N':visit(e[1])
    visit(183)
    frozen.update(set(s.NODES)-ax)
    return frozen

def options(nodes,origins,scope):
    options=s.rotate.options(nodes)
    if scope=='all':return options
    freeze=frozen_origins()
    return [op for op in options if not(origins.get(op[0],set())&freeze)]

def metrics(nodes,root):
    @lru_cache(None)
    def prefix(n):
        e=nodes[n][0]
        return 1+(prefix(e[1]) if e[0]=='N' else 0)
    return sum(max(0,prefix(n)-6) for n in nodes),s.rotate.zero_metrics(nodes,root)

def shortened(table):
    assert table[58,0]==(0,'L',74)
    return {(q,b):(w,d,84 if t==74 else t) for (q,b),(w,d,t) in table.items() if q!=74}

def graph_count(table):
    seen=set();todo=[64]
    while todo:
        q=todo.pop()
        if q==254 or q in seen:continue
        seen.add(q);todo.extend(table[q,b][2] for b in (0,1))
    return len(seen)

def evaluate(nodes,root,origins,out,name,limit=150000):
    results=[]
    for allocation in ('identity','identity_greedy','origin','greedy','fresh'):
        try:table,emission=s.emit(nodes,root,origins,allocation)
        except (KeyError,IndexError,AssertionError) as ex:
            results.append(dict(allocation=allocation,outcome='emit_failure',reason=str(ex)));continue
        table=shortened(table)
        runtime,used=s.check(table,nodes,root)
        rr=dict(allocation=allocation,runtime=runtime,graph_states=graph_count(table),runtime_states=len({q for q,b in used|s.audit.BOX_PAIRS}),outcome='runtime_pass' if runtime['passed'] else 'runtime_failure')
        if runtime['passed']:
            startup,bootused=s.boot(table,limit)
            rr['boot']=startup
            if startup['outcome']=='zero_root':
                table=s.prune(table,used|bootused)
                rr.update(outcome='passed',working_states=len(table)//2)
                (out/(name+'_'+allocation+'.tm')).write_bytes(s.audit.encode(table))
                print('VERIFIED',name,allocation,'states',len(table)//2,'boot',startup['steps'],flush=True)
            else:rr['outcome']='boot_'+startup['outcome']
        results.append(rr)
    (out/(name+'_checks.json')).write_text(json.dumps(results,indent=2)+'\n')
    return results

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=100000);ap.add_argument('--seed',type=int,default=252);ap.add_argument('--output',type=Path,default=HERE/'zero_results');ap.add_argument('--input',type=Path);ap.add_argument('--beam',type=int,default=0);ap.add_argument('--max-nodes',type=int,default=230);ap.add_argument('--scope',choices=['all','opaque'],default='all')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);begun=time.monotonic();rng=random.Random(a.seed)
    nodes,root,origins=s.NODES,s.ROOT,{n:{n} for n in s.NODES}
    if a.input:
        d=json.loads(a.input.read_text());nodes={int(q):tuple(map(tuple,p)) for q,p in d['nodes'].items()};root=d['root'];origins={int(q):set(v) for q,v in d['origins'].items()}
    initial=nodes,root,origins;bad,zm=metrics(nodes,root)
    best=(bad,len(nodes));best_data=initial;zero_best=999;history=[];tested=set();checks=[]
    if a.beam:
        frontier=[(bad,len(nodes),nodes,root,origins,[])];seen={s.fingerprints(nodes)[root]}
        for depth in range(a.iterations):
            proposals=[]
            for _,__,nodes,root,origins,hist in frontier:
                for n,e,kind in options(nodes,origins,a.scope):
                    nn,r,oo=s.mutate(nodes,root,n,e,origins);b,z=metrics(nn,r)
                    if len(nn)>a.max_nodes or z[1]>7 or z[2]>39:continue
                    fp=s.fingerprints(nn)[r]
                    if fp in seen:continue
                    seen.add(fp);hh=hist+[[n,e,kind]]
                    proposals.append((b,len(nn),nn,r,oo,hh))
            if not proposals:break
            # A small cardinality penalty avoids expensive zero-free grammars.
            proposals.sort(key=lambda v:(2*v[0]+max(0,v[1]-203),v[1],v[0]))
            frontier=proposals[:a.beam]
            for b,ncount,nn,r,oo,hist in frontier:
                if (b,ncount)<best:
                    best=(b,ncount);best_data=nn,r,oo
                    save(a.output/'best_zero_grammar.json',nn,r,oo,hist,dict(bad=b,nodes=ncount,depth=depth))
                if b==0 and ncount<zero_best:
                    zero_best=ncount;name=f'zero_{depth}_{ncount}'
                    save(a.output/(name+'.json'),nn,r,oo,hist,dict(bad=b,nodes=ncount,depth=depth))
                    checks.append(dict(name=name,results=evaluate(nn,r,oo,a.output,name)))
            print('BEAM',depth,'best',best,'front',frontier[0][:2],'seen',len(seen),'sec',round(time.monotonic()-begun,1),flush=True)
        save(a.output/'beam_result.json',*best_data,[],dict(best=best,seen=len(seen),checks=checks))
        return
    current_energy=10*bad+len(nodes)
    for i in range(a.iterations):
        if i and i%10000==0:
            nodes,root,origins=best_data;bad,_=metrics(nodes,root);current_energy=10*bad+len(nodes);history=[]
        opts=options(nodes,origins,a.scope)
        if not opts:break
        n,e,kind=rng.choice(opts);nn,r,oo=s.mutate(nodes,root,n,e,origins);b,z=metrics(nn,r)
        if z[1]>7 or z[2]>39 or len(nn)>a.max_nodes:continue
        energy=10*b+len(nn);temperature=.03+.3*(1-(i%10000)/10000)
        if energy<=current_energy or rng.random()<math.exp((current_energy-energy)/temperature):
            nodes,root,origins=nn,r,oo;bad=b;current_energy=energy;history.append([n,e,kind])
        if (b,len(nn))<best:
            best=(b,len(nn));best_data=nn,r,oo
            save(a.output/'best_zero_grammar.json',nn,r,oo,history,dict(bad=b,nodes=len(nn),iteration=i))
            print('BETTER',i,b,len(nn),'sec',round(time.monotonic()-begun,1),flush=True)
        if b==0 and len(nn)<zero_best:
            zero_best=len(nn);name=f'zero_{i}_{len(nn)}'
            save(a.output/(name+'.json'),nn,r,oo,history,dict(bad=b,nodes=len(nn),iteration=i))
            checks.append(dict(name=name,results=evaluate(nn,r,oo,a.output,name)))
        if i%5000==0:print('ANNEAL',i,'best',best,'current',bad,len(nodes),'sec',round(time.monotonic()-begun,1),flush=True)
    save(a.output/'anneal_result.json',*best_data,[],dict(best=best,checks=checks))

def save(path,nodes,root,origins,history,extra):
    path.write_text(json.dumps(dict(root=root,nodes=nodes,origins={n:sorted(v) for n,v in origins.items()},history=history,summary=extra),indent=2)+'\n')

if __name__=='__main__':main()
