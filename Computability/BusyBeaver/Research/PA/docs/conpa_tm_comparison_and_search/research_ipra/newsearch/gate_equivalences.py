#!/usr/bin/env python3
"""Classically equivalent arrangements of the established guarded gate.

The original h1 and all six heads are preserved, so classical reasoning
with the fixed falsity code 1 remains available without circularity.
"""
from wrapper_dictionary import *
def ev(t,x):
    if isinstance(t,str):return x[t]
    _,a,b=t;return not ev(a,x) or ev(b,x)
def patterns():
    out=set()
    for p in itertools.permutations('DVQ'):
        for shape in (0,1):
            for signs in itertools.product((0,1),repeat=5):
                a,b,c=[v.N(x) if signs[i] else x for i,x in enumerate(p)]
                if shape==0:t=v.I(a,b);t=v.N(t) if signs[3] else t;t=v.I(t,c)
                else:t=v.I(b,c);t=v.N(t) if signs[3] else t;t=v.I(a,t)
                if signs[4]:t=v.N(t)
                if all(ev(t,dict(zip('DVQ1',bits+(False,))))==(bits[0] and bits[1] and not bits[2])
                    for bits in itertools.product((False,True),repeat=3)):out.add(t)
    return sorted(out,key=lambda t:(str(t).count("'1'"),str(t)))
def instantiate(t,d):
    if isinstance(t,str):return d.get(t,t)
    tag,a,b=t;return tag,instantiate(a,d),instantiate(b,d)
def parts(flags):
    a,b,c='HDA'
    delta=v.I(v.E(a,b),v.U(c,v.E(a,b)))
    vacuity=v.I(v.M(a,b),v.U(c,v.M(a,b)))
    point=v.I(c,v.M(c,b))
    x=v.I(v.M(a,b),point)
    if flags&1:x=v.I(c,v.I(v.M(a,b),v.M(c,b)))
    y=v.I(v.M(c,b),c)
    separation=v.U(b,v.conjunction(y,x) if flags&2 else v.conjunction(x,y))
    q=v.U(c,v.I(point,v.N(separation)) if flags&4 else v.I(separation,v.N(point)))
    return {'D':delta,'V':vacuity,'Q':q}
if __name__=='__main__':
    random.seed(117799);start=time.time();scored=[];seen=set()
    for pi,pt in enumerate(patterns()):
        for flags in range(8):
            f=instantiate(pt,parts(flags));w=prefix+sum(map(v.emit,v.heads()),[])+v.emit(f)+suffix
            if tuple(w) in seen:continue
            seen.add(tuple(w));label=f'gate_p{pi}_f{flags}';parsed=parse(w,96,6);raw=parsed[0][0]
            scored.append((raw,label,w,parsed,pt,flags))
            print('PARSE',label,'raw',raw,'tokens',len(w),'sec',time.time()-start,flush=True)
    scored.sort(key=lambda x:x[0]);(OUT/'gate_equivalences_parse.json').write_text(json.dumps([
        {'raw':r,'label':l,'word':w,'pattern':p,'flags':f} for r,l,w,_,p,f in scored],indent=2))
    candidates=[]
    for vi,(raw,label,w,parsed,pt,flags) in enumerate(scored):
        if raw>70:continue
        best=(999,None)
        for k,(raw,p) in enumerate(parsed):
            if raw>70:continue
            for t in assemble([trees[q] for q in p],600):
                c,n,f,choices=cost(t)
                if c<best[0]:
                    best=c,t;print('BEST',label,c,n,f,'variant',vi,'part',k,'sec',time.time()-start,flush=True)
                    d=encode(t);d.update({'wrapper':label,'cost':[c,n,f],'pattern':pt,'flags':flags})
                    (OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                    if c<62:check(t,label)
        if best[0]<=64:candidates.append([best[0],label,best[1],pt,flags])
    candidates.sort(key=lambda x:x[0]);print('START ROTATIONS',[(c,l) for c,l,*_ in candidates],flush=True)
    for cycle in range(160):
        slot=cycle%len(candidates);bc,label,t,pt,flags=candidates[slot]
        c,n,f,choices=cost(t)
        for j in range(1800):
            node=random.choice(choices);rs=list(rots(node))
            if not rs:continue
            nt=replace(t,node,random.choice(rs)) if random.random()<.6 else rocc(t)
            nc,nn,nf,nchoices=cost(nt);temp=.1+.55*(1-j/1800)
            if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
            if c<candidates[slot][0]:
                candidates[slot]=[c,label,t,pt,flags];print('BESTROT',label,c,n,f,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True)
                d=encode(t);d.update({'wrapper':label,'cost':[c,n,f],'pattern':pt,'flags':flags})
                (OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                if c<62:check(t,label)
        print('CYCLE',cycle,[(c,l) for c,l,*_ in candidates],'sec',time.time()-start,flush=True)
