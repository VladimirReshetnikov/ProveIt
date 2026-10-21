#!/usr/bin/env python3
"""Compute a finite product-domain invariant for the supplied K219 source.

Bits0..7 denote the exact values0..7; bit8 denotes all values at least8.
Seed, every transfer, and every CFG edge are rechecked after the fixed point.
Selected Cartesian-minimum fixtures need not occur on the actual blank run.
"""
from pathlib import Path
import argparse,collections,json,sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True,help='Extracted K221 package')
    ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required.')
    sys.path.insert(0,str(args.baseline.resolve()/'portable'))
    import source_language as s
    sites=json.loads(args.sites.read_text());graph,_=s.graph_arithmetic(sites)
    assert graph==s.graph_intervals(sites)
    cutoff=8;top=1<<cutoff;mask=top-1
    inc=lambda b:((b&mask)<<1)|(b&top)
    dec=lambda b:(b>>1)|(b&top)
    seed=[3,0,0,0,3,0,0,0,0]
    facts=[[0]*9 for _ in sites];facts[0]=[1<<x for x in seed]
    queue=collections.deque([0]);queued={0};updates=0
    while queue:
        i=queue.popleft();queued.remove(i);updates+=1
        field=facts[i];_,op,arg=sites[i]
        for bit,target in enumerate(graph[i][1]):
            value=field.copy()
            if op=='CI':value[arg]=inc(value[arg])
            if op=='CD':
                value[arg]=(value[arg]&1)if bit==0 else dec(value[arg]&~1)
                if not value[arg]:continue
            merged=[a|b for a,b in zip(facts[target],value)]
            if merged!=facts[target]:
                facts[target]=merged
                if target not in queued:queue.append(target);queued.add(target)
    assert all((1<<x)&f for x,f in zip(seed,facts[0]))
    checks=0;cases=[];excluded=[]
    for i,(_,op,arg)in enumerate(sites):
        field=facts[i]
        if any(x==0 for x in field):
            excluded.extend([[i,p]for p in((False,True)if op=='CD'else(False,))]);continue
        for bit,target in enumerate(graph[i][1]):
            value=field.copy()
            if op=='CI':value[arg]=inc(value[arg])
            if op=='CD':value[arg]=(value[arg]&1)if bit==0 else dec(value[arg]&~1)
            if op=='CD'and not value[arg]:continue
            assert all(a|b==b for a,b in zip(value,facts[target]));checks+=1
        for positive in((False,True)if op=='CD'else(False,)):
            admitted=op!='CD'or field[arg]&(~1 if positive else 1)
            (cases if admitted else excluded).append([i,positive])
    result=dict(cutoff=cutoff,facts=facts,seed=seed,admitted_cases=cases,
                excluded_cases=excluded,closure_checks=checks,updates=updates)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps(dict(sites=len(sites),admitted_cases=len(cases),excluded_cases=excluded,
                         closure_checks=checks,updates=updates)))

if __name__=='__main__':main()
