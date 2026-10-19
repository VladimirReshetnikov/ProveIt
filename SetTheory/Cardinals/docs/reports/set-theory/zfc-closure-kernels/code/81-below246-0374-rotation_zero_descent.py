#!/usr/bin/env python3
"""Greedy descent in maximal-zero-run multiplicity with exact control repair."""
import json
import time
import argparse
from collections import Counter
import rotation_control_repair as cr
r=cr.r

def zero_score(root):
    ls=r.flatten(root)
    counts=Counter(max(map(len,p.split('1'))) for p,_,_ in ls)
    return tuple(counts[n] for n in range(20,0,-1))

def describe(score):return {str(20-i):n for i,n in enumerate(score) if n}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start',type=str)
    parser.add_argument('--target-zero',type=int,default=6)
    parser.add_argument('--max-steps',type=int,default=24)
    parser.add_argument('--prefix',default='rotation_zero')
    args=parser.parse_args()
    started=time.monotonic();raw=r.a.PROGRAM.read_bytes()
    ls,cases,by,first=r.a.read_program(raw);original=r.load(raw)
    root=r.rotate(original,95,'left')
    if args.start:
        data=json.loads((r.OUT/args.start).read_text());memo={}
        def rec(i):
            if i in memo:return memo[i]
            e=data['entries'][str(i)]
            memo[i]=r.mk(('N',rec(e[1]),rec(e[2]))) if e[0]=='N' else r.mk(tuple(e))
            return memo[i]
        root=rec(data['root'])
    records=[];tried=0
    for step in range(args.max_steps):
        current=zero_score(root);options=[]
        for p in r.reachable(root):
            for direction in ('left','right'):
                c=r.rotate(root,p,direction)
                if c is None:continue
                if len(r.reachable(c))>203:continue
                score=zero_score(c)
                if score<current:options.append((score,p,direction,c))
        options.sort()
        best=None
        for score,p,direction,c in options:
            outcome=cr.repair(c,ls,cases,by,first);tried+=1
            if outcome is None:continue
            final,meta=outcome
            if meta['unique_pairs']>202:continue
            best=final,meta,p,direction,score;break
        if best is None:break
        root,meta,p,direction,score=best
        meta.update(step=step+1,pivot=p,direction=direction,zero_histogram=describe(score))
        record={k:v for k,v in meta.items() if k!='edits'};records.append(record)
        r.dump_graph(root,r.OUT/f'{args.prefix}_candidate_{step+1:02}.json',meta)
        print(json.dumps(record),flush=True)
        if meta['maximum_zero_run']<=args.target_zero:break
    out=dict(steps=len(records),tried=tried,seconds=time.monotonic()-started,
        final_zero_histogram=describe(zero_score(root)),records=records)
    (r.OUT/f'{args.prefix}_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
