#!/usr/bin/env python3
"""Add repeated macro strings to a dictionary retaining all original fold pairs."""
import sys,collections,random,heapq,time,itertools
from frozen_rotate import *

W=''.join(WORD);counts=collections.Counter(t for p,t in paths(BASE))
rep={t for t,n in counts.items() if n>1}|FROZEN;rep.add(('i','i'))
D={''.join(expand(t)):t for t in rep};D.update({x:x for x in W})
freq=collections.Counter(W[i:j] for i in range(len(W)) for j in range(i+2,len(W)+1))
CANDS=[s for s,n in freq.items() if n>1 and s not in D]

def parse(w,dd,seed=0):
    cost={len(w):0};choice={}
    for i in range(len(w)-1,-1,-1):
        cost[i],choice[i]=min((1+cost[i+len(s)],s) for s in dd if w.startswith(s,i))
    seq=[];i=0
    while i<len(w):s=choice[i];seq.append(dd[s]);i+=len(s)
    def build(s):
        if len(s)==1:return s[0]
        k=len(s)//2;return build(s[:k]),build(s[k:])
    return build(seq),cost[0]

def nc(t):
    ns=nodes(t)
    return len(ns)-int(('i','i') in ns),len(FROZEN-ns)

if __name__=='__main__':
    start=time.time();best=68;beam=[((),D)];seen=set();width=int(sys.argv[1]) if len(sys.argv)>1 else 100
    for depth in range(4):
        nxt=[]
        for hist,d in beam:
            for s in CANDS:
                if s in hist:continue
                hh=tuple(sorted(hist+(s,)))
                if hh in seen:continue
                seen.add(hh)
                p,k=parse(s,d);dd=dict(d);dd[s]=p;t,m=parse(W,dd)
                n,f=nc(t)
                if n<best:
                    best=n
                    print('best',n,'patterns',hh,'missingfrozen',f,'secs',round(time.time()-start,3),flush=True)
                    output(t,Path(__file__).with_name('dictionary_best.json'))
                nxt.append(((n,f,m,sum(map(len,hh))),hh,dd))
        nxt.sort(key=lambda x:x[0])
        beam=[(h,d) for _,h,d in nxt[:width]]
        print('depth',depth+1,'tried',len(seen),'best',best,'beam best',nxt[0][0],'secs',round(time.time()-start,3),flush=True)
