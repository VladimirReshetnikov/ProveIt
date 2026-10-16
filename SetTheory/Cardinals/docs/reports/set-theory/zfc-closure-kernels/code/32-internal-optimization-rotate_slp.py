#!/usr/bin/env python3
"""Reassociate closed register subprograms using a backend-derived count proxy.

Research prototype. A checked finite RM bisimulation is emitted by a separate
driver. Individual proposals are not compiled here. The retained control must
be compiled separately. No binary compiler correctness claim is made by this
search alone.
"""
from __future__ import annotations
import argparse
from collections import Counter
import importlib
import json
import math
from pathlib import Path
import random
import sys
import time


def load(path):
    d = json.loads(Path(path).read_text())
    return {int(k): tuple(v) for k, v in d['nodes'].items()}, {int(k): v for k,v in d['names'].items()}


def canonical(nodes, names):
    memo, bypair, out, nm, active = {}, {}, {}, {}, set()
    def edge(e):
        return 'ENode '+str(visit(int(e.split()[1]))) if e.startswith('ENode ') else e
    def visit(q):
        if q in memo: return memo[q]
        if q in active: raise ValueError('cyclic decoder')
        active.add(q)
        pair=tuple(edge(e) for e in nodes[q])
        active.remove(q)
        if pair not in bypair:
            ident=len(out)
            bypair[pair]=ident;out[ident]=pair;nm[ident]=names.get(q,'rot_'+str(q))
        memo[q]=bypair[pair]
        return memo[q]
    root=visit(0)
    order=[root]+[i for i in range(len(out)) if i!=root]
    ids={q:i for i,q in enumerate(order)}
    result={ids[q]:tuple('ENode '+str(ids[int(e.split()[1])]) if e.startswith('ENode ') else e for e in out[q]) for q in order}
    newnames={ids[q]:nm[q] for q in order};newnames[0]='main().0'
    # Backend names must be unique even when a historical name was reused.
    seen=set()
    for q in newnames:
        if newnames[q] in seen: newnames[q]+='_rot_'+str(q)
        seen.add(newnames[q])
    return result,newnames


def facts(nodes):
    bounds={}; depths={}
    def be(e):
        kind,*v=e.split();n=int(v[0]) if v else 0
        if kind=='ENode': return bound(n)
        if kind=='EDecnz': return (1,0)
        if kind=='EBreak': return (n,0)
        if kind=='EContinue': return (0,n)
        return (0,0)
    def bound(q):
        if q not in bounds:
            a,b=map(be,nodes[q]); bounds[q]=(max(0,a[0]-1,b[0]),max(0,a[1],b[1]-1))
        return bounds[q]
    def depth(q):
        if q not in depths:
            e=nodes[q][0]
            depths[q]=1+(depth(int(e.split()[1])) if e.startswith('ENode ') else 0)
        return depths[q]
    for q in nodes:bound(q);depth(q)
    opts=[]
    for q,(left,right) in nodes.items():
        if left.startswith('ENode '):
            a,b=nodes[int(left.split()[1])]; c=right
            if all(be(e)==(0,0) for e in (a,b,c)):opts.append((q,0,a,b,c))
        if right.startswith('ENode '):
            a=left;b,c=nodes[int(right.split()[1])]
            if all(be(e)==(0,0) for e in (a,b,c)):opts.append((q,1,a,b,c))
    return max(2,max(depths.values())),opts


def rotate(nodes,names,opt):
    q,d,a,b,c=opt
    nn=dict(nodes);nm=dict(names);fresh=max(nodes)+1
    if d==0:
        nn[fresh]=(b,c);nn[q]=(a,'ENode '+str(fresh))
    else:
        nn[fresh]=(a,b);nn[q]=('ENode '+str(fresh),c)
    nm[fresh]='rotation_'+str(fresh)
    return canonical(nn,nm)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--iterations',type=int,default=20000)
    ap.add_argument('--seed',type=int,default=20261016)
    ap.add_argument('--window',type=int,default=2000)
    args=ap.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    nodes,names=canonical(*load(args.input));dep,opts=facts(nodes)
    rng=random.Random(args.seed);initial=len(nodes)+55+dep
    best=(nodes,names);bestv=initial;cur=best;cv=initial
    histogram=Counter();records=[];t0=time.monotonic()
    for it in range(args.iterations+1):
        if it:
            if it%args.window==0: cur=best;cv=bestv;_,opts=facts(cur[0])
            candidate=rotate(*cur,rng.choice(opts));d,oo=facts(candidate[0])
            v=len(candidate[0])+55+d
            histogram[v]+=1
            # Backend-derived count expression; this does not invoke the compiler.
            temp=.05+.7*(1-(it%args.window)/args.window)
            if v<=cv or rng.random()<math.exp((cv-v)/temp):cur=candidate;cv=v;opts=oo
            if v>=bestv:continue
            best=candidate;bestv=v
        record={'iteration':it,'states_predicted':bestv,'nodes':len(best[0]),'left_depth':facts(best[0])[0], 'elapsed_seconds':time.monotonic()-t0}
        records.append(record);print(json.dumps(record),flush=True)
        (out/'best.dag.json').write_text(json.dumps({'nodes':best[0],'names':best[1],'root':0},indent=2)+'\n')
        (out/'search.json').write_text(json.dumps({'input':str(args.input),'seed':args.seed,'iterations_completed':it,'records':records},indent=2)+'\n')
    (out/'search.json').write_text(json.dumps({'input':str(args.input),'seed':args.seed,'iterations_completed':args.iterations,'records':records,'histogram':histogram,'elapsed_seconds':time.monotonic()-t0,'criterion':'all three rotation components have break and continue bounds zero'},indent=2)+'\n')
    print(json.dumps({'done':args.iterations,'best':bestv,'elapsed_seconds':time.monotonic()-t0}),flush=True)


if __name__=='__main__': main()
