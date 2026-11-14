#!/usr/bin/env python3
from pathlib import Path
exec(Path(__file__).with_name('wrapper_search.py').read_text().split('OUT=Path')[0])
OUT=Path(__file__).resolve().parent/'fusion_anneal';OUT.mkdir(exist_ok=True)
random.seed(628771);start=time.time();candidates=[]
for p in sorted((OUT.parent/'fused_unconditional').glob('assembled_*.json')):
    d=json.loads(p.read_text())
    if d['cost'][0]<=65:
        t=read_grammar(p);candidates.append([cost(t)[0],p.stem,t,d['meta']])
print('INITIAL',[(c,n) for c,n,*_ in candidates],flush=True)
for cycle in range(36):
    slot=cycle%len(candidates);_,label,t,meta=candidates[slot];c,n,f,choices=cost(t)
    for j in range(3000):
        node=random.choice(choices);opts=list(rots(node))
        if not opts:continue
        nt=replace(t,node,random.choice(opts)) if random.random()<.65 else rocc(t)
        nc,nn,nf,nchoices=cost(nt);temp=.12+.7*(1-j/3000)
        if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
        if c<candidates[slot][0]:
            candidates[slot]=[c,label,t,meta]
            print('BEST',label,c,n,f,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True)
            d=encode(t);d['cost']=[c,n,f];d['meta']=meta
            (OUT/(label+'.json')).write_text(json.dumps(d))
            if c<62:check(t,label)
    print('CYCLE',cycle,label,'bests',[(a,b) for a,b,*_ in candidates],'seconds',time.time()-start,flush=True)
(OUT/'receipt.json').write_text(json.dumps({'results':[(c,n) for c,n,*_ in candidates],'seconds':time.time()-start}))
