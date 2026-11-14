#!/usr/bin/env python3
"""Explore provable truth antecedents on the guarded gate."""
import sys,json,random,math,time,itertools,collections
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/logic'));sys.path.insert(0,str(BASE/'work/optimize196'))
import logical_variant_search as v
from layout import *
ns=raw_nodes();tree,word,prefix,suffix=v.read_source(ROOT)
IG=len(prefix)+sum(len(v.emit(h)) for h in v.heads());EG=len(word)-len(suffix)
def attrs(t):
    if isinstance(t,str):return attrs(ns[t])
    if not isnode(t):return(0,0,0)
    h1,l1,m1=attrs(t[0]);h2,l2,m2=attrs(t[1]);return(1+max(h1,h2),l1+1,max(1+l1,m1,m2))
MA={x:attrs(x) for x in set(MACROS)|{BREAK}}
def cost(t):
    intern={}
    def rec(t):
        if not isnode(t):return MA[t]
        if t in intern:return intern[t]
        h1,l1,m1=rec(t[0]);h2,l2,m2=rec(t[1]);ans=(1+max(h1,h2),l1+1,max(1+l1,m1,m2));intern[t]=ans;return ans
    h,l,m=rec(t);n=len(intern)
    if m>6 or h>38:return(n+max(0,m-6)*2+max(0,h-38),n,0,list(intern))
    r,idx,sh=build(t);ops=opportunities_fast(r,sh);folds=len(max_matching(ops))
    return n-folds,n,folds,list(intern)
def encode(t):
    rs={};ids={}
    def rec(t):
        if not isnode(t):return t
        if t in ids:return ids[t]
        a,b=map(rec,t);q='g'+str(len(rs));rs[q]=[a,b];ids[t]=q;return q
    rt=rec(t);return {'root':rt,'rules':rs}
def rewrite(t,before,after):
    i=0
    def rec(t):
        nonlocal i
        if not isnode(t):
            ix=i;i+=1
            if ix==IG:
                for x in reversed(before):t=(x,t)
            if ix==EG-1:
                for x in after:t=(t,x)
            return t
        return tuple(map(rec,t))
    return rec(t)
def replace(t,x,y):
    if t==x:return y
    if isnode(t):return tuple(replace(s,x,y) for s in t)
    return t
def rots(t):
    if isnode(t[0]):a,b=t[0];yield(a,(b,t[1]))
    if isnode(t[1]):b,c=t[1];yield((t[0],b),c)
def rocc(t):
    paths=[]
    def collect(s,p):
        if not isnode(s):return
        if isnode(s[0]) or isnode(s[1]):paths.append(p)
        collect(s[0],p+(0,));collect(s[1],p+(1,))
    collect(t,());p=random.choice(paths)
    def rec(s,p):
        if not p:return random.choice(list(rots(s)))
        if p[0]:return(s[0],rec(s[1],p[1:]))
        return(rec(s[0],p[1:]),s[1])
    return rec(t,p)
def check(t,label):
    rows,index,shape=build(t);sites,ins,cs=source(t)
    print('CANDIDATE',label,'raw',len(rows)//2,'maxpath',max(len(p) for p,*_ in sites),flush=True)
    # Find a compatible order for all advertised folds, using exact contexts.
    goal=len(rows)//2-195
    seen=set()
    def search(rr,ss,hist):
        if len(hist)>=goal:
            ans=validate(rr,cs);print('VALIDATE',label,ans,flush=True)
            if ans['ok']:
                (OUT/'candidate.json').write_text(json.dumps({'rows':[[q,b,*a] for (q,b),a in sorted(rr.items())],'sites':sites,'instructions':ins,'history':hist,'wrapper':label,'grammar':encode(t),'validation':ans}));raise SystemExit()
            return
        options=opportunities_fast(rr,ss)
        if len(hist)+len(max_matching(options))<goal:return
        for a,b,opts in options:
            for acts in itertools.product(*opts):
                nr=fold(rr,a,b,acts);ns=dict(ss);ns.pop(a)
                key=tuple(sorted(nr.items()))
                if key in seen:continue
                seen.add(key);search(nr,ns,hist+[(a,b,acts)])
    search(rows,shape,[])
OUT=Path(__file__).resolve().parent/'wrappers';OUT.mkdir(exist_ok=True)
random.seed(424242);start=time.time();candidates=[]
wrappers=[]
for n in range(1,5):wrappers.append((f'truth{n}',['node49']*n,['node65']*n))
for n in range(1,3):wrappers.append((f'dneg{n}',[],(['node49',v.INC,'node65']*2)*n))
for r in 'DHA':wrappers.append(('all'+r,[],[v.VARS[r],'node65',v.INC,v.INC]))
for label,before,after in wrappers:
    t=rewrite(tree,before,after);c,n,f,choices=cost(t)
    print('INITIAL',label,c,n,f,flush=True);candidates.append([c,label,t])
    (OUT/(label+'.json')).write_text(json.dumps(encode(t)))
best=62
for cycle in range(180):
    _,label,t=candidates[cycle%len(candidates)];c,n,f,choices=cost(t)
    for j in range(2500):
        node=random.choice(choices);opts=list(rots(node))
        if not opts:continue
        nt=replace(t,node,random.choice(opts)) if random.random()<.6 else rocc(t)
        nc,nn,nf,nchoices=cost(nt);temp=.12+.6*(1-j/2500)
        if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
        if c<candidates[cycle%len(candidates)][0]:
            candidates[cycle%len(candidates)]=[c,label,t]
            print('BEST',label,c,n,f,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True)
            (OUT/(label+'.json')).write_text(json.dumps(encode(t)))
            if c<62:check(t,label)
    print('CYCLE',cycle,label,'bests',[(a,b) for a,b,_ in candidates],'seconds',time.time()-start,flush=True)
