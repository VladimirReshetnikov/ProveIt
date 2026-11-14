#!/usr/bin/env python3
"""Explore U/E tag transposition on PA196's AX grammar."""
import sys,json,random,math,time,itertools
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/optimize196'))
from layout import *
from grammar import axword
ns=raw_nodes()
def tree(s):
    if isinstance(s,str) and s.startswith('x'):
        return tuple(map(tree,ns[s]))
    return s
original=tree('x67');word=axword();INC=('leaf','inc',1)
groups=[]
i=0
while i<len(word):
    if word[i]=='node65':
        j=i+1
        while j<len(word) and word[j]==INC:j+=1
        if j-i-1 in (2,3):groups.append((i+1,j))
        i=j
    else:i+=1
def edit_tree(choices):
    replacements={}
    for (a,b),choice in zip(groups,choices):
        replacements[a+choice]=(INC,INC) if b-a==2 else None
    cursor=0
    def rec(t):
        nonlocal cursor
        if not isnode(t):
            pos=cursor;cursor+=1
            return replacements.get(pos,t)
        a,b=map(rec,t)
        if a is None:return b
        if b is None:return a
        return(a,b)
    return rec(original)
def attrs(t):
    if isinstance(t,str):return attrs(ns[t])
    if not isnode(t):return(0,0,0)
    h1,l1,m1=attrs(t[0]);h2,l2,m2=attrs(t[1]);return(1+max(h1,h2),l1+1,max(1+l1,m1,m2))
MACROATTRS={x:attrs(x) for x in set(MACROS)|{BREAK}}
def cost(t):
    intern={}
    def rec(t):
        if not isnode(t):return MACROATTRS[t]
        if t in intern:return intern[t]
        h1,l1,m1=rec(t[0]);h2,l2,m2=rec(t[1]);ans=(1+max(h1,h2),l1+1,max(1+l1,m1,m2));intern[t]=ans;return ans
    h,l,m=rec(t);n=len(intern)
    if m>6 or h>38:return(n+max(0,m-6)*2+max(0,h-38),n,0,list(intern))
    rows,index,shape=build(t);folds=len(max_matching(opportunities_fast(rows,shape)))
    return n-folds,n,folds,list(intern)
def encode(t):
    rules={};ids={}
    def rec(t):
        if not isnode(t):return t
        if t in ids:return ids[t]
        a,b=map(rec,t);q='g'+str(len(rules));rules[q]=[a,b];ids[t]=q;return q
    rt=rec(t);return {'root':rt,'rules':rules}
def replace(t,x,y):
    if t==x:return y
    if isnode(t):return tuple(replace(s,x,y) for s in t)
    return t
def rotations(t):
    if isnode(t[0]):a,b=t[0];yield(a,(b,t[1]))
    if isnode(t[1]):b,c=t[1];yield((t[0],b),c)
OUT=Path(__file__).resolve().parent/'tag_swap';OUT.mkdir(exist_ok=True)
random.seed(20261113);start=time.time();best=999;bestt=None
print('groups',groups,'sizes',[b-a for a,b in groups],flush=True)
for iteration in range(5000):
    if iteration<6:
        choices=[iteration%2 if b-a==2 else iteration//2 for a,b in groups]
    else:choices=[random.randrange(b-a) for a,b in groups]
    t=edit_tree(choices);c,n,f,rs=cost(t)
    if c<best:
        best,bestt=c,t;print('BEST mapped',c,n,f,'iteration',iteration,'seconds',time.time()-start,flush=True)
        (OUT/'best.json').write_text(json.dumps(encode(t)))
    if best<62:break
for cycle in range(100):
    t=bestt;c,n,f,rs=cost(t)
    for iteration in range(3000):
        node=random.choice(rs);rots=list(rotations(node))
        if not rots:continue
        nt=replace(t,node,random.choice(rots));nc,nn,nf,nrs=cost(nt)
        temp=.15+.7*(1-iteration/3000)
        if nc<=c or random.random()<math.exp((c-nc)/temp):
            t,c,n,f,rs=nt,nc,nn,nf,nrs
        if c<best:
            best,bestt=c,t;print('BEST rotate',c,n,f,'cycle',cycle,'iteration',iteration,'seconds',time.time()-start,flush=True)
            (OUT/'best.json').write_text(json.dumps(encode(t)))
            if best<62:raise SystemExit()
    print('cycle',cycle,'best',best,'seconds',time.time()-start,flush=True)
