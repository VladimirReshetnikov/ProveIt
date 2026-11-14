#!/usr/bin/env python3
"""Conservative h1/h5 weakenings using the otherwise unused AX parameter.

All h1 forms recover the original h1 at a fixed simple setting of A; this
retains explosion noncircularly. Thus changes are not an unproved shorter
logical basis. Primitive source macros and the engine are unchanged.
"""
from wrapper_dictionary import *
def h1(d,h):return v.I(v.exists(d,v.U(d,h)),h)
def rename(t,m):
    if isinstance(t,str):return m.get(t,t)
    k,a,b=t;return k,rename(a,m),rename(b,m)
def forms():
    old=v.heads();one=old[0];five=old[4]
    h1s=[('old',one),('outerA',v.I('A',one)),
        ('innerA',v.I(one[1],v.I('A','H'))),
        ('argAH',h1('D',v.I('A','H'))),
        ('argHA',h1('D',v.I('H','A'))),
        ('argOr',h1('D',v.I(v.I('A','H'),'H'))),
        ('argPeirce',h1('D',v.I(v.I('H','A'),'H')))]
    # For h5, A -> N(W) and W -> N(A) are pure antecedent exchanges.
    w=five[1]
    h5s=[('old',five),('outerA',v.I('A',five)),('innerA',v.I(w,v.N('A')))]
    return h1s,h5s
if __name__=='__main__':
    random.seed(666751);start=time.time();scored=[];seen=set();base=v.heads()
    perms=list(itertools.permutations('DHA'))
    for i,(l1,f1) in enumerate(forms()[0]):
        for j,(l5,f5) in enumerate(forms()[1]):
            if i==j==0:continue
            for p1,m1 in enumerate(perms):
                for p5,m5 in enumerate(perms):
                    hh=list(base);hh[0]=rename(f1,dict(zip('DHA',m1)));hh[4]=rename(f5,dict(zip('DHA',m5)))
                    w=prefix+sum(map(v.emit,hh),[])+v.emit(v.gate())+suffix
                    if tuple(w) in seen:continue
                    seen.add(tuple(w));label=f'head_{l1}_{p1}_{l5}_{p5}'
                    parsed=parse(w,40,4);raw=parsed[0][0]
                    scored.append((raw,label,w,parsed,(l1,p1,l5,p5)))
            print('GROUP',l1,l5,'best',min(x[0] for x in scored),'seen',len(scored),'sec',time.time()-start,flush=True)
    scored.sort(key=lambda x:x[0]);(OUT/'head_weakenings_parse.json').write_text(json.dumps([
        {'raw':r,'label':l,'word':w,'meta':m} for r,l,w,_,m in scored],indent=2))
    print('PARSE BEST',[(r,l) for r,l,*_ in scored[:30]],flush=True)
    candidates=[]
    for vi,(raw,label,w,parsed,meta) in enumerate(scored):
        if raw>70:continue
        best=(999,None)
        for k,(raw,p) in enumerate(parsed):
            if raw>70:continue
            for t in assemble([trees[q] for q in p],600):
                c,n,f,choices=cost(t)
                if c<best[0]:
                    best=c,t;print('BEST',label,c,n,f,'variant',vi,'part',k,'sec',time.time()-start,flush=True)
                    d=encode(t);d.update({'wrapper':label,'cost':[c,n,f],'meta':meta});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                    if c<62:check(t,label)
        if best[0]<=64:candidates.append([best[0],label,best[1],meta])
    candidates.sort(key=lambda x:x[0]);print('START ROTATIONS',[(c,l) for c,l,*_ in candidates],flush=True)
    for cycle in range(180):
        if not candidates:break
        slot=cycle%len(candidates);bc,label,t,meta=candidates[slot]
        c,n,f,choices=cost(t)
        for j in range(1800):
            node=random.choice(choices);rs=list(rots(node))
            if not rs:continue
            nt=replace(t,node,random.choice(rs)) if random.random()<.6 else rocc(t)
            nc,nn,nf,nchoices=cost(nt);temp=.1+.55*(1-j/1800)
            if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
            if c<candidates[slot][0]:
                candidates[slot]=[c,label,t,meta];print('BESTROT',label,c,n,f,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True)
                d=encode(t);d.update({'wrapper':label,'cost':[c,n,f],'meta':meta});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                if c<62:check(t,label)
        print('CYCLE',cycle,[(c,l) for c,l,*_ in candidates],'sec',time.time()-start,flush=True)
