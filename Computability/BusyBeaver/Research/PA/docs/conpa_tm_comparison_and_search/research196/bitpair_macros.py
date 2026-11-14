#!/usr/bin/env python3
"""Counter-program experiments for 2^a(2b+1)-1 pairing."""
import sys,itertools,json,collections
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/optimize196'))
from grammar import raw_nodes
from layout import isnode
nodes=raw_nodes()
def leaf(op,arg=None):return ('leaf',op,arg)
def inc(r):return leaf('inc',r)
def dec(r):return leaf('dec',r)
def cont(k):return leaf('continueTo',k)
def seq(*xs):
    if len(xs)==1:return xs[0]
    return (xs[0],seq(*xs[1:]))
def close_loop(t):
    # Replace tagged self-continuations by the number of right edges back.
    def walk(s,p):
        if s==('self',):return cont(sum(p))
        if not isnode(s):return s
        return tuple(walk(child,p+(i,)) for i,child in enumerate(s))
    return walk(t,())
def loop(r,*body):return close_loop((dec(r),seq(*body,('self',))))
def drain(r,to,n=1):return loop(r,*([inc(to)]*n))
def raw_count(t):
    intern=set();leaves=set();size=0
    def rec(t):
        nonlocal size
        if not isnode(t):leaves.add(t);size+=1;return
        intern.add(t)
        rec(t[0]);rec(t[1])
    rec(t);return len(intern),len(leaves),size
def expand(s,replace=None):
    replace=replace or {}
    if isinstance(s,str):
        if s in replace:return replace[s]
        return tuple(expand(x,replace) for x in nodes[s])
    return s
def pair_core(positive=False,orient=0):
    # Input T=b, X=a, Y=0. Output T=X=0, Y=pair(a,b).
    doubleTY=drain(1,7,2);doubleYT=drain(7,1,2);transferTY=drain(1,7)
    if positive:return seq(doubleTY,inc(7),loop(6,doubleYT,transferTY))
    return seq(doubleTY,loop(6,doubleYT,transferTY,inc(7)))
def pop_core(reg):
    # Number of trailing ones = v2(n+1); quotient at first zero = second.
    restore=drain(7,reg)
    inner=(dec(reg),seq((dec(reg),seq(inc(7),('self',))),inc(6),restore,('self',)))
    return seq(close_loop(inner),restore)
def resolve(t):
    sites=[]
    def walk(s,p):
        if isnode(s):walk(s[0],p+(0,));walk(s[1],p+(1,))
        else:sites.append((p,*s[1:]))
    walk(t,())
    def locate(p):
        for i,(q,*_) in enumerate(sites):
            if q[:len(p)]==p or p[:len(q)]==q and not any(p[len(q):]):return i
        raise ValueError(p)
    def cut(p,b,n):
        for i in range(len(p)-1,-1,-1):
            if p[i]==b:
                n-=1
                if n==0:return p[:i]
        raise ValueError((p,b,n))
    def after(p):
        for i in range(len(p)-1,-1,-1):
            if p[i]==0:return locate(p[:i]+(1,))
        return len(sites)
    codes=[]
    for p,op,a in sites:
        if op=='inc':codes.append(('inc',a,after(p)))
        elif op=='dec':codes.append(('dec',a,after(cut(p,0,1)),after(p)))
        elif op=='continueTo':codes.append(('jump',locate(cut(p,1,a))))
        elif op=='breakTo':codes.append(('jump',after(cut(p,0,a))))
        else:raise ValueError(op)
    return codes
def run(codes,regs,limit=1000000):
    pc=0;r=list(regs)
    for n in range(limit):
        if pc==len(codes):return r,n
        c=codes[pc]
        if c[0]=='inc':r[c[1]]+=1;pc=c[2]
        elif c[0]=='dec':
            if r[c[1]]==0:pc=c[2]
            else:r[c[1]]-=1;pc=c[3]
        else:pc=c[1]
    raise RuntimeError((regs,r,pc))
def verify_pair(t,positive=False):
    # Add a harmless final inc/decrement so final unguarded loop dec resolves.
    codes=resolve(seq(t,inc(0)))
    for a in range(8):
        for b in range(8):
            r=[0]*9;r[1]=b;r[6]=a
            out,n=run(codes,r)
            ex=[0]*9;ex[0]=1;ex[7]=(1<<a)*(2*b+1)-(not positive)
            assert out==ex,(a,b,out,ex)
def verify_pop(t,reg):
    codes=resolve(seq(t,inc(0)))
    for n in range(256):
        r=[0]*9;r[reg]=n;out,steps=run(codes,r)
        m=n+1;a=0
        while m%2==0:a+=1;m//=2
        b=(m-1)//2
        ex=[0]*9;ex[0]=1;ex[reg]=b;ex[6]=a
        assert out==ex,(n,out,ex)
if __name__=='__main__':
    original=expand('node172');print('original whole',raw_count(original))
    for name in ['node17','node32','node46','node49','node65']:
        print('original',name,raw_count(expand(name)))
    pair=pair_core();verify_pair(pair);popW=pop_core(2);verify_pop(popW,2);popL=pop_core(8);verify_pop(popL,8)
    print('new pair',raw_count(pair),'popW',raw_count(popW),'popL',raw_count(popL))
    replace={'node46':pair,'node17':popW,'node32':popL}
    t=expand('node172',replace);print('new whole',raw_count(t))
    Path(__file__).with_name('bitpair_count.json').write_text(json.dumps({'original':raw_count(original),'new':raw_count(t)}))
