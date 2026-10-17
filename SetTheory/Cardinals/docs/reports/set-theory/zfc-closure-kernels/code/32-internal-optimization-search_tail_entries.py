#!/usr/bin/env python3
"""Finite prefix search for spare-tail writers using existing runtime states.

The entry is the end-of-file transition old97/read0. A successful local
prefix must return to old112 on the preceding zero, without visiting cells
further left. This makes every accepted prefix independent of register values.
It does not check blank startup or establish a consistency-machine bound.
"""
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
file=ROOT/'vendor/upstream/ZF/m253/tools/generate_candidate.py'
spec=importlib.util.spec_from_file_location('public253',file)
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
base=g.patched_rows(ROOT/'vendor/upstream/ZF/m254/machine/zfc_254.tm')
base[49,1]=(0,'R',64)
base={k:v for k,v in base.items() if k[0]!=5}

def parse(bits):
    values=[];i=0
    while i<len(bits):
        if bits[i]!=0:return None
        i+=1;n=0
        while i<len(bits) and bits[i]:i+=1;n+=1
        if not n:return None
        values.append(n-1)
    return values

def trial(write,direction,target):
    table=dict(base);table[97,0]=(write,direction,target)
    q,h,ones=97,0,set()
    seen=set()
    for steps in range(1000):
        if steps and q==112 and h==-1:
            if -1 in ones:return None
            end=max(ones,default=-1)
            right=[int(x in ones) for x in range(end+1)]
            tail=parse([0,1]+right)
            if tail is not None:return dict(transition=[write,direction,target],steps=steps,spare_append=tail,right_ones=sorted(ones))
            return None
        if h<-1 or h>100 or q==254:return None
        conf=(q,h,tuple(sorted(ones)))
        if conf in seen:return None
        seen.add(conf)
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    return None

def main():
    results=[]
    for q in sorted({q for q,b in base}):
        for w in (0,1):
            for d in ('L','R'):
                r=trial(w,d,q)
                if r is not None:results.append(r)
    out=Path(__file__).with_name('tail_entry_results.json')
    out.write_text(json.dumps({'candidates_checked':1008,'local_prefixes':results,'blank_bootstrap_claim':False},indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
