#!/usr/bin/env python3
"""Transport original AX subtrees to conservative logical gate wrappers.

The source language and fixed engine are unchanged. Every claimed table must
pass all symbolic contracts; the initial grammar score alone is not a machine.
"""
from pathlib import Path
import sys,json,time,random,math,itertools,collections
from functools import lru_cache
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/logic'))
sys.path.insert(0,str(BASE/'work/optimize196'))
from layout import *
import logical_variant_search as v
ns=raw_nodes()
initial,word,prefix,suffix=v.read_source(ROOT)
OUT=Path(__file__).with_name('wrappers');OUT.mkdir(exist_ok=True)
_original_machine=machine()
build.__globals__['machine']=lambda:_original_machine
macroattrs={}
def attrs(t):
    if isinstance(t,str):
        if t in macroattrs:return macroattrs[t]
        a=attrs(ns[t]);macroattrs[t]=a;return a
    if not isnode(t):return 0,0,0
    h1,l1,m1=attrs(t[0]);h2,l2,m2=attrs(t[1])
    return 1+max(h1,h2),l1+1,max(1+l1,m1,m2)
for m in MACROS:attrs(m)
def stats(t):
    used={}
    def rec(t):
        if not isnode(t):return attrs(t)
        if t in used:return used[t]
        h1,l1,m1=rec(t[0]);h2,l2,m2=rec(t[1])
        a=1+max(h1,h2),l1+1,max(1+l1,m1,m2);used[t]=a;return a
    a=rec(t);return len(used),a,list(used)
def cost(t):
    n,(h,l,m),choices=stats(t)
    if m>6 or h>38:return n+2*max(0,m-6)+max(0,h-38),n,0,choices
    r,idx,sh=build(t);ops=opportunities_fast(r,sh)
    return n-len(max_matching(ops)),n,len(max_matching(ops)),choices
def encode(t):
    rs={};ids={}
    def rec(t):
        if not isnode(t):return t
        if t in ids:return ids[t]
        a,b=map(rec,t);q='g'+str(len(rs));rs[q]=[a,b];ids[t]=q;return q
    rt=rec(t);return {'root':rt,'rules':rs}
def replace(t,x,y):
    if t==x:return y
    if isnode(t):return replace(t[0],x,y),replace(t[1],x,y)
    return t
def rots(t):
    if isnode(t[0]):a,b=t[0];yield a,(b,t[1])
    if isnode(t[1]):b,c=t[1];yield (t[0],b),c
def rocc(t):
    ps=[]
    def collect(t,p):
        if not isnode(t):return
        if isnode(t[0]) or isnode(t[1]):ps.append(p)
        collect(t[0],p+(0,));collect(t[1],p+(1,))
    collect(t,());p=random.choice(ps)
    def rec(t,p):
        if not p:return random.choice(list(rots(t)))
        if p[0]:return t[0],rec(t[1],p[1:])
        return rec(t[0],p[1:]),t[1]
    return rec(t,p)
trees=[];ids={};words=[];masks=[]
def intern(t):
    if t in ids:return ids[t]
    if isnode(t):
        a,b=map(intern,t);w=words[a]+words[b];mask=masks[a]|masks[b]
    else:w=(t,);mask=0
    q=len(trees);ids[t]=q;trees.append(t);words.append(w)
    masks.append(mask|(1<<q) if isnode(t) else 0);return q
intern(initial)
def parse(word,B=128,K=12):
    n=len(word);opts=[]
    for i in range(n):opts.append([q for q,w in enumerate(words) if tuple(word[i:i+len(w)])==w])
    dp=[{} for _ in range(n+1)];dp[0][0]=()
    for i in range(n):
        beam=sorted(dp[i].items(),key=lambda x:x[0].bit_count()+len(x[1]))[:B]
        dp[i]={}
        for mask,parts in beam:
            for q in opts[i]:
                j=i+len(words[q]);m=mask|masks[q];p=parts+(q,)
                if m not in dp[j] or len(p)<len(dp[j][m]):dp[j][m]=p
    return [(m.bit_count()+len(p)-1,p) for m,p in sorted(dp[n].items(),key=lambda x:x[0].bit_count()+len(x[1]))[:K]]
def assemble(parts,count=4000):
    n=len(parts);aa=list(map(attrs,parts))
    @lru_cache(None)
    def splits(i,j,b):
        if i+1==j:return (-1,) if aa[i][1]<=b and aa[i][2]<=6 else ()
        if b<=0:return ()
        return tuple(k for k in range(i+1,j) if splits(i,k,b-1) and splits(k,j,6))
    if not splits(0,n,6):return
    def sample(i,j,b):
        if i+1==j:return parts[i]
        k=random.choice(splits(i,j,b));return sample(i,k,b-1),sample(k,j,6)
    for _ in range(count):yield sample(0,n,6)
def check(t,label):
    rows,index,shape=build(t);sites,ins,cs=source(t);goal=len(rows)//2-195
    print('CANDIDATE',label,'raw',len(rows)//2,'neededfolds',goal,flush=True)
    seen=set();calls=0
    def search(rr,ss,hist):
        nonlocal calls
        calls+=1
        if len(hist)>=goal:
            ans=validate(rr,cs);print('VALIDATE',label,ans,flush=True)
            if ans['ok']:
                (OUT/'candidate195.json').write_text(json.dumps({'rows':[[q,b,*a] for (q,b),a in sorted(rr.items())],
                    'sites':sites,'instructions':ins,'history':hist,'wrapper':label,'grammar':encode(t),'validation':ans},indent=2))
                raise SystemExit()
            return
        if calls>2000:return
        options=opportunities_fast(rr,ss)
        if len(hist)+len(max_matching(options))<goal:return
        for a,b,opts in options:
            for acts in itertools.product(*opts):
                nr=fold(rr,a,b,acts);ns=dict(ss);ns.pop(a);key=tuple(sorted(nr.items()))
                if key in seen:continue
                seen.add(key);search(nr,ns,hist+[(a,b,acts)])
    search(rows,shape,[])
if __name__=='__main__':
    random.seed(926771);start=time.time();gate=v.gate()
    variants=[('dneg'+str(k),v.emit(v.N(v.N(gate))) if k==1 else v.emit(v.N(v.N(v.N(v.N(gate)))))) for k in (1,2)]
    variants += [('all'+r,v.emit(v.U(r,gate))) for r in 'DHA']
    candidates=[]
    for label,gword in variants:
        w=prefix+sum(map(v.emit,v.heads()),[])+gword+suffix
        best=(999,None);parsed=parse(w,256,18)
        print('PARSED',label,[c for c,p in parsed],'sec',time.time()-start,flush=True)
        for pi,(raw,p) in enumerate(parsed):
            if raw>74:continue
            for t in assemble([trees[q] for q in p],3000):
                c,n,f,choices=cost(t)
                if c<best[0]:
                    best=c,t
                    print('BEST',label,c,n,f,'partchoice',pi,'sec',time.time()-start,flush=True)
                    d=encode(t);d.update({'wrapper':label,'cost':[c,n,f]});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                    if c<62:check(t,label)
        candidates.append([best[0],label,best[1]])
    for cycle in range(150):
        slot=cycle%len(candidates);bc,label,t=candidates[slot]
        if t is None:continue
        c,n,f,choices=cost(t)
        for j in range(2500):
            node=random.choice(choices);rs=list(rots(node))
            if not rs:continue
            nt=replace(t,node,random.choice(rs)) if random.random()<.6 else rocc(t)
            nc,nn,nf,nchoices=cost(nt);temp=.1+.6*(1-j/2500)
            if nc<=c or random.random()<math.exp((c-nc)/temp):t,c,n,f,choices=nt,nc,nn,nf,nchoices
            if c<candidates[slot][0]:
                candidates[slot]=[c,label,t]
                print('BESTROT',label,c,n,f,'cycle',cycle,'iter',j,'sec',time.time()-start,flush=True)
                d=encode(t);d.update({'wrapper':label,'cost':[c,n,f]});(OUT/(label+'.json')).write_text(json.dumps(d,indent=2))
                if c<62:check(t,label)
        print('CYCLE',cycle,[(c,l) for c,l,_ in candidates],'sec',time.time()-start,flush=True)
