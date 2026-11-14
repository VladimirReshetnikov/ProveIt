#!/usr/bin/env python3
"""Jointly bracket four disjoint closed-sequence regions of PA196."""
from pathlib import Path
import sys, json, functools, collections, time, math, random, itertools
import optimize_closed as O
NAMES=('x67','node21','node36','node168')
ENTRIES=((89,1),(75,0),(127,0),(133,1))
START=tuple(O.openax(O.RAW[n]) for n in NAMES)
# This outer copy root was not in the <=150 fixed-macro catalog.
O.FREE[START[3]]=37;O.TAGS[START[3]]={0,1}
PREFIXES=[]
for name in NAMES:
    ps=[]
    def find(t,p=()):
        if t==O.RAW[name]:ps.append(p);return
        if t[0]!='leaf':find(t[0],p+(0,));find(t[1],p+(1,))
    find(O.ROOT);assert len(ps)==1,(name,ps)
    PREFIXES.append(ps[0])
TRAIL=[len(p)-len(''.join(map(str,p)).rstrip('0')) for p in PREFIXES]

def shape_ok(t):
    return all(O.zero_shape(x)[1]<=6 and z+O.zero_shape(x)[0]<=6 for x,z in zip(t,TRAIL))
def make(t,pruned=True):
    m=O.BASE.copy();new={}
    def emit(x,bit):
        if x in O.FREE and bit in O.TAGS[x]:return O.FREE[x]
        if isinstance(x,str):
            if x in O.TAGS and bit not in O.TAGS[x]:raise ValueError(('wrong atom context',x,bit))
            return O.ATOMS[x]
        if x in new:return new[x]
        def row(y,b):return (0,-1,131 if b else 5) if y=='B' else (b,1,emit(y,b))
        a,b=x;r0=row(a,0);r1=row(b,1)
        q=1000+len(new);new[x]=q;m[q,0]=r0;m[q,1]=r1
        return q
    entries=[]
    for expr,key in zip(t,ENTRIES):
        w,d,old=m[key];entry=emit(expr,w);m[key]=(w,d,entry);entries.append(entry)
    return (O.prune(m) if pruned else m),new,entries
@functools.lru_cache(maxsize=10000)
def evaluate(t):
    if not shape_ok(t):return 1000,0,0,()
    try:m,new,entries=make(t)
    except ValueError:return 1000,0,0,()
    protected={q for q,b in O.S.ENGINE_ROWS}|{m[k][2] for k in O.S.ENGINE_ROWS if k in m}|{0,O.S.ROOT}
    opts=O.F.candidates(m,{q for q,b in m if q not in protected})
    sel,tested=O.F.best_subset(m,opts)
    return len(m)//2-len(sel),len(m)//2,len(sel),tuple(sel)
def tree(t):
    root=O.ROOT
    for name,expr in zip(NAMES,t):root=O.C.replace(root,O.RAW[name],O.raw(expr))
    return root

def output(t,path):
    rules={};rev={}
    def go(q):
        if isinstance(q,str):return q
        if q in rev:return rev[q]
        a,b=map(go,q);n=f'r{len(rules)}';rev[q]=n;rules[n]=(a,b)
        return n
    roots=list(map(go,t))
    data=dict(kind='four regions',names=NAMES,roots=roots,rules=rules,tokens={n:n for n in O.ATOMS if n!='i'},evaluation=evaluate(t))
    path.write_text(json.dumps(data,indent=2))
def validate(t,path):
    m,new,entries=make(t);score,n,c,sel=evaluate(t);mm,mu=O.F.fold(m,sel)
    tr=tree(t);result=O.C.check(mm,tr,True)
    path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(mm.items())))
    path.with_suffix('.check.json').write_text(json.dumps(result,indent=2));path.with_suffix('.sites.json').write_text(json.dumps(O.S.flatten(tr)))
    return result
@functools.lru_cache(None)
def bracket(xs):
    if len(xs)==1:return (xs[0],)
    return tuple((a,b) for k in range(1,len(xs)) for a in bracket(xs[:k]) for b in bracket(xs[k:]))

def main():
    budget=int(sys.argv[1])if len(sys.argv)>1 else 200000
    seed=int(sys.argv[2])if len(sys.argv)>2 else 711643
    rng=random.Random(seed);start=time.monotonic();best=196;bestt=START;ties=[];ties_seen=0
    print('BASE',evaluate(START),'prefixes',PREFIXES,flush=True)
    outers=list(itertools.product(*(bracket(tuple(O.expand(x)))for x in START[1:])))
    for k,outer in enumerate(outers):
        t=(START[0],)+outer;s,n,c,ds=evaluate(t)
        if s<best:
            best=s;bestt=t;print('OUTER BEST',best,k,n,c,flush=True)
        if s==best:ties.append(t)
        if s<196:
            p=Path(__file__).with_name(f'regions_outer_{s}_{k}.json');output(t,p);result=validate(t,p);print('VALIDATE',result,flush=True)
            if not result['failures']:return
    print('OUTERS',len(outers),'best',best,'ties',len(ties),flush=True)
    t=bestt;score=best;seen=set(ties)
    for it in range(budget):
        if it%3000==0:t=rng.choice([START,bestt]+ties);score=evaluate(t)[0]
        cand=list(t)
        for _ in range(2 if rng.random()<.16 else 1):
            j=rng.choices(range(4),[80,8,8,4])[0]
            p,q=rng.choice(O.paths(cand[j]));a,b=q
            if rng.randrange(2):
                if not isinstance(a,tuple):continue
                u,v=a;alt=(u,(v,b))
            else:
                if not isinstance(b,tuple):continue
                u,v=b;alt=((a,u),v)
            cand[j]=O.replace(cand[j],q,alt)if rng.random()<.72 else O.replace_one(cand[j],p,alt)
        cand=tuple(cand)
        if it%10000==0:print('progress',it,'best',best,'current',score,'seconds',round(time.monotonic()-start,1),flush=True)
        if cand in seen:continue
        seen.add(cand)
        s,n,c,ds=evaluate(cand)
        temp=.5*(1-(it%3000)/3000)+.05
        if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;score=s
        if s<=best:
            if s<best:best=s;bestt=cand;ties=[];ties_seen=0;print('BEST',best,n,c,it,flush=True)
            ties_seen+=1
            if len(ties)<150:ties.append(cand)
            elif rng.randrange(ties_seen)<150:ties[rng.randrange(150)]=cand
            if s<196:
                p=Path(__file__).with_name(f'regions_{s}_{seed}_{it}.json');output(cand,p);result=validate(cand,p);print('VALIDATE',result,flush=True)
                if not result['failures']:break
    output(bestt,Path(__file__).with_name(f'regions_best_{seed}.json'))
    for i,t in enumerate(ties[:30]):output(t,Path(__file__).with_name(f'regions_tie_{seed}_{i}.json'))
    print('DONE',best,len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
