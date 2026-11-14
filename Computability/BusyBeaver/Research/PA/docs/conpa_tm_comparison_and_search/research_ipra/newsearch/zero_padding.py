#!/usr/bin/env python3
"""Numerically neutral padding: PUSH0 PUSH0 C = PUSH0 (I(0,0)=0)."""
from wrapper_dictionary import *
if __name__=='__main__':
    random.seed(499031);start=time.time();scored=[]
    pos=[i for i,x in enumerate(word) if x=='node49'];assert len(pos)==8
    for mask in range(1,1<<len(pos)):
        w=[];j=0
        for x in word:
            w.append(x)
            if x=='node49':
                if mask>>j&1:w+=['node49','node65']
                j+=1
        label=f'zero_padding_{mask}';parsed=parse(w,80,6);raw=parsed[0][0]
        scored.append((raw,label,w,parsed,mask))
        if mask%16==0:print('PARSE',mask,'best',min(s[0] for s in scored),'sec',time.time()-start,flush=True)
    scored.sort(key=lambda x:x[0]);(OUT/'zero_padding_parse.json').write_text(json.dumps([
        {'raw':r,'label':l,'word':w,'mask':m} for r,l,w,_,m in scored],indent=2))
    print('PARSE BEST',[(r,l) for r,l,*_ in scored[:30]],flush=True)
    candidates=[]
    for vi,(raw,label,w,parsed,mask) in enumerate(scored):
        if raw>70:continue
        best=(999,None)
        for k,(raw,p) in enumerate(parsed):
            if raw>70:continue
            for t in assemble([trees[q] for q in p],500):
                c,n,f,choices=cost(t)
                if c<best[0]:
                    best=c,t;print('BEST',label,c,n,f,'variant',vi,'part',k,'sec',time.time()-start,flush=True)
                    d=encode(t);d.update({'wrapper':label,'cost':[c,n,f],'mask':mask});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                    if c<62:check(t,label)
        if best[0]<=64:candidates.append([best[0],label,best[1],mask])
    candidates.sort(key=lambda x:x[0]);print('START ROTATIONS',[(c,l) for c,l,*_ in candidates],flush=True)
    for cycle in range(160):
        if not candidates:break
        slot=cycle%len(candidates);bc,label,t,mask=candidates[slot]
        c,n,f,choices=cost(t)
        for j in range(1800):
            node=random.choice(choices);rs=list(rots(node))
            if not rs:continue
            nt=replace(t,node,random.choice(rs)) if random.random()<.6 else rocc(t)
            nc,nn,nf,nchoices=cost(nt);temp=.1+.55*(1-j/1800)
            if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
            if c<candidates[slot][0]:
                candidates[slot]=[c,label,t,mask];print('BESTROT',label,c,n,f,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True)
                d=encode(t);d.update({'wrapper':label,'cost':[c,n,f],'mask':mask});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                if c<62:check(t,label)
        print('CYCLE',cycle,[(c,l) for c,l,*_ in candidates],'sec',time.time()-start,flush=True)
