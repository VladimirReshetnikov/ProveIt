#!/usr/bin/env python3
"""Inductive register bounds for any supplied nine-counter binary source tree.

Python standard library only; no repository paths or third-party imports.
Compute: script sites.json --output invariant.json
Replay:  script sites.json --verify invariant.json --output verification.json
The certificate overapproximates every unbounded run from the calibrated seed.
"""
from pathlib import Path
from collections import deque
import argparse,hashlib,json,sys,time

def require(test,message):
    if not test:raise ValueError(message)

def source(path):
    rows=json.loads(path.read_text())
    require(isinstance(rows,list) and rows,'Empty source')
    for row in rows:
        require(isinstance(row,list) and len(row)==3,'Malformed source row')
        pc,op,arg=row
        require(isinstance(pc,str) and pc and set(pc)<={'0','1'},'Malformed path')
        require(op in ('CI','CD','CB','CC','CH'),'Unknown instruction')
        if op in ('CI','CD'):require(type(arg)is int and 0<=arg<9,'Bad register')
        elif op in ('CB','CC'):require(type(arg)is int and arg>=1,'Bad control argument')
        else:require(arg is None,'Bad halt')
    require(rows==sorted(rows),'Source is not in tree order')
    index={p:i for i,(p,op,arg)in enumerate(rows)}
    require(len(index)==len(rows),'Duplicate source paths')
    prefixes={p[:k]for p in index for k in range(len(p))}
    require(not prefixes.intersection(index),'A source leaf is also internal')
    require(all(p+b in index or p+b in prefixes for p in prefixes for b in '01'),'Incomplete tree')
    depth=max(map(len,index))
    def resolve(bits):
        p='';k=0
        while p not in index:
            p+=bits[k]if k<len(bits)else'0';k+=1
            require(k<=depth,'Unresolved successor')
        require('1'not in bits[k:],'Nonzero unconsumed successor suffix')
        return index[p]
    def increment(p):
        if not p:return''
        return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')
    def strip(p,b,n):
        for k in range(len(p)-1,-1,-1):
            if p[k]==b:
                n-=1
                if not n:return p[:k]
        return''
    graph=[]
    for p,op,arg in rows:
        if op=='CH':successors=[]
        elif op=='CI':successors=[resolve(increment(p))]
        elif op=='CD':successors=[resolve(increment(p)),resolve(increment(strip(p,'0',1)))]
        elif op=='CB':successors=[resolve(increment(strip(p,'0',arg)))]
        else:successors=[resolve(strip(p,'1',arg))]
        graph.append((op,arg,successors))
    return rows,graph,resolve('')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('sites',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--verify',type=Path);ap.add_argument('--cutoff',type=int,default=8)
    ap.add_argument('--modulus',type=int,default=2);args=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Assertions must remain enabled')
    started=time.monotonic();rows,graph,entry=source(args.sites)
    source_hash=hashlib.sha256(args.sites.read_bytes()).hexdigest()
    old=json.loads(args.verify.read_text())if args.verify else None
    C,M=(old['cutoff'],old['modulus'])if old else(args.cutoff,args.modulus)
    require(type(C)is int and C>=4 and type(M)is int and M>=1,'Bad abstraction parameters')
    N=C+M;ALL=(1<<N)-1;seed=[3,0,0,0,3,0,0,0,0]
    def bucket(n):return n if n<C else C+(n%M)
    def representatives(i):
        return[i]if i<C else[n for n in range(C,C+2*M)if bucket(n)==i]
    # The only exceptional decrement is C -> C-1. A second representative
    # for that residue also covers the non-boundary result. All higher values
    # have the same residue transition; this is exact finite abstraction.
    inc=[sum(1<<j for j in{bucket(n+1)for n in representatives(i)})for i in range(N)]
    dec=[sum(1<<j for j in{bucket(n-1)for n in representatives(i)if n>0})for i in range(N)]
    def transfer(mask,images):
        out=0
        for i in range(N):
            if mask>>i&1:out|=images[i]
        return out
    def outputs(i,values):
        op,arg,succ=graph[i]
        if op=='CH':return[]
        if op=='CI':
            v=values.copy();v[arg]=transfer(v[arg],inc);return[(succ[0],v)]
        if op=='CD':
            out=[]
            if values[arg]&~1:
                v=values.copy();v[arg]=transfer(v[arg]&~1,dec);out.append((succ[0],v))
            if values[arg]&1:
                v=values.copy();v[arg]=1;out.append((succ[1],v))
            return out
        return[(succ[0],values)]
    updates=0
    if old:
        require(old['source_sha256']==source_hash,'Wrong certificate source hash')
        require(old['seed']==seed and old['entry']==entry,'Wrong seed or entry')
        facts=old['facts']
    else:
        facts=[None]*len(rows);facts[entry]=[1<<bucket(n)for n in seed]
        todo=deque([entry]);queued={entry}
        while todo:
            i=todo.popleft();queued.remove(i)
            for j,v in outputs(i,facts[i]):
                before=facts[j];after=v.copy()if before is None else[x|y for x,y in zip(before,v)]
                if after!=before:
                    facts[j]=after;updates+=1
                    if j not in queued:todo.append(j);queued.add(j)
    # Independent acceptance pass. No worklist status is trusted here.
    require(len(facts)==len(rows),'Wrong certificate length')
    for v in facts:
        require(v is None or isinstance(v,list)and len(v)==9 and all(type(x)is int and 0<x<=ALL for x in v),'Bad register mask')
    require(facts[entry]is not None and all((facts[entry][r]>>bucket(n))&1 for r,n in enumerate(seed)),'Seed is outside invariant')
    checks=0
    for i,v in enumerate(facts):
        if v is None:continue
        for j,w in outputs(i,v):
            require(facts[j]is not None and all(x&~y==0 for x,y in zip(w,facts[j])),'Transition leaves invariant')
            checks+=1
    dead=[i for i,v in enumerate(facts)if v is None];disabled=[]
    for i,(pc,op,arg)in enumerate(rows):
        if op=='CD'and facts[i]is not None:
            if not facts[i][arg]&1:disabled.append([i,'zero'])
            if not facts[i][arg]&~1:disabled.append([i,'positive'])
    nip=[dict(site_index=i,path=pc,R6_mask=facts[i][6]if facts[i]else None)
         for i,(pc,op,arg)in enumerate(rows)if pc=='11101001010'and(op,arg)==('CI',6)]
    result=dict(status='INDUCTIVE_REGISTER_BUCKET_PASS',cutoff=C,modulus=M,buckets=N,
        source_sha256=source_hash,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_sites=len(rows),entry=entry,seed=seed,facts=facts,updates=updates,closure_checks=checks,
        dead_sites=dead,disabled_decrement_guards=disabled,nip_entry=nip,
        inc_bucket_masks=inc,dec_bucket_masks=dec,seconds=time.monotonic()-started,
        scope='All finite source prefixes from the exact calibrated seed, with unbounded natural registers; a Cartesian overapproximation, not exact reachability.')
    if args.verify:result['replayed_certificate_sha256']=hashlib.sha256(args.verify.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='facts'},indent=2))

if __name__=='__main__':main()
