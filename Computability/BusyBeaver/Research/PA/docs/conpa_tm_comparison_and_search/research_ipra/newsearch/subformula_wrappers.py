#!/usr/bin/env python3
"""Insert I(0,X) at individual gate subformula sites, preserving equivalence."""
from wrapper_dictionary import *
def emit(t):
    if t=='0':return ['node49']
    if isinstance(t,str):return v.emit(t)
    tag,a,b=t;return emit(a)+emit(b)+['node65']+[v.INC]*tag
def astsites(t,p=()):
    yield p,t
    if isinstance(t,tuple):
        yield from astsites(t[1],p+(1,))
        yield from astsites(t[2],p+(2,))
def astreplace(t,p,u):
    if not p:return u
    z=list(t);z[p[0]]=astreplace(z[p[0]],p[1:],u);return tuple(z)
def flatten(t):
    return flatten(t[0])+flatten(t[1]) if isnode(t) else [t]
if __name__=='__main__':
    random.seed(774662);start=time.time();gate=v.gate();scored=[];seen=set()
    for p,x in astsites(gate):
        f=astreplace(gate,p,v.I('0',x));label='truth_at_'+('root' if not p else ''.join(map(str,p)))
        w=prefix+sum(map(v.emit,v.heads()),[])+emit(f)+suffix
        if tuple(w) in seen:continue
        seen.add(tuple(w));parsed=parse(w,64,5);raw=parsed[0][0]
        scored.append((raw,label,w,parsed))
        print('PARSE',label,'raw',raw,'parts',len(parsed[0][1]),'sec',time.time()-start,flush=True)
    scored.sort(key=lambda x:x[0]);(OUT/'subformula_parse.json').write_text(json.dumps([{'raw':r,'label':l,'word':w} for r,l,w,_ in scored],indent=2))
    candidates=[]
    for vi,(raw,label,w,parsed) in enumerate(scored):
        if raw>70:continue
        best=(999,None)
        for pi,(raw,p) in enumerate(parsed):
            if raw>70:continue
            for t in assemble([trees[q] for q in p],400):
                c,n,f,choices=cost(t)
                if c<best[0]:
                    best=c,t;print('BEST',label,c,n,f,'variant',vi,'part',pi,'sec',time.time()-start,flush=True)
                    d=encode(t);d.update({'wrapper':label,'cost':[c,n,f]});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                    if c<62:check(t,label)
        candidates.append([best[0],label,best[1]])
    candidates.sort(key=lambda x:x[0]);print('START ROTATIONS',[(c,l) for c,l,_ in candidates],flush=True)
    candidates=[x for x in candidates if x[0]<=64]
    for cycle in range(150):
        slot=cycle%len(candidates);bc,label,t=candidates[slot]
        if t is None:continue
        c,n,f,choices=cost(t)
        for j in range(1200):
            node=random.choice(choices);rs=list(rots(node))
            if not rs:continue
            nt=replace(t,node,random.choice(rs)) if random.random()<.6 else rocc(t)
            nc,nn,nf,nchoices=cost(nt);temp=.1+.45*(1-j/1200)
            if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
            if c<candidates[slot][0]:
                candidates[slot]=[c,label,t];print('BESTROT',label,c,n,f,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True)
                d=encode(t);d.update({'wrapper':label,'cost':[c,n,f]});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                if c<62:check(t,label)
        print('CYCLE',cycle,[(c,l) for c,l,_ in candidates],'sec',time.time()-start,flush=True)
