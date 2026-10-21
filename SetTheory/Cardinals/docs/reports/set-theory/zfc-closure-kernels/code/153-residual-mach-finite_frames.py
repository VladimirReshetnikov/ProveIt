#!/usr/bin/env python3
"""Exact native complete-frame simulator used for finite counterexamples.

Frame conventions are adapted from pinned K221 independent_runtime.py.
This module imports no symbolic runtime proof engine.
"""
import csv,json,hashlib
from pathlib import Path


PHY=(6,2,0,4,3,7,8,5,1)

def frame(pc,logical,spares,gap=0):
    physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    ones={-1,64+gap}|{i for i,b in enumerate(pc)if b=='1'}
    pos=65+gap
    for value in physical+list(spares):
        pos+=1;ones.update(range(pos,pos+value+1));pos+=value+1
    return ones

def inc(pc):
    if not pc:return '',1
    n=len(pc);v=int(pc,2)+1
    return format(v%(1<<n),'0'+str(n)+'b'),int(v==1<<n)

def strip(pc,bit,n):
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            n-=1
            if n==0:return pc[:i]
    return ''

def expected(site,logical,spares):
    pc,op,arg=site;logical=list(logical);spares=list(spares);gap=0;shift=0
    if op=='CI':logical[arg]+=1;spares.append(1);pc,shift=inc(pc)
    elif op=='CD' and logical[arg]:logical[arg]-=1;gap=1;pc,shift=inc(pc)
    elif op in('CD','CB'):pc,shift=inc(strip(pc,'0',1 if op=='CD'else arg))
    elif op=='CC':pc=strip(pc,'1',arg)
    else:raise ValueError('Counterexample uses a nonhalting primitive')
    return 84,-shift,{x-shift for x in frame(pc,logical,spares,gap+shift)}

def dispatch(q,h,ones):
    if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
    right=sorted(x for x in ones if x>=h+52)
    if not right or right[0]<h+64:return False
    p=right[0]+1;last=max(ones);values=[]
    while p<last:
        if p in ones or p+1 not in ones:return False
        start=p+1;p=start
        while p in ones:p+=1
        values.append(p-start-1)
    return p==last+1 and len(values)>=10

def run(table,ones,q=84,limit=100000):
    ones=set(ones);h=0;trace=[]
    for tick in range(limit+1):
        # This ray condition is itself an exact proof of subsequent divergence.
        ray=(q,0)in table and table[q,0][1:]==(1,q)and h>max(ones,default=-1)
        if tick and(dispatch(q,h,ones)or q==254 or ray):
            return(q,h,ones),trace,'right_blank_ray'if ray else'dispatch'if q==84 else'halt'
        if tick==limit:return(q,h,ones),trace,'limit'
        bit=int(h in ones);write,move,target=table[q,bit]
        trace.append((tick,q,h,bit,write,move,target))
        if write:ones.add(h)
        else:ones.discard(h)
        q=target;h+=move

def conf(x):return {'state':x[0],'head':x[1],'one_cells':sorted(x[2])}

def write_trace(path,rows):
    with path.open('w',newline='')as f:
        w=csv.writer(f);w.writerow(['tick','state','head','read','write','move','target']);w.writerows(rows)
    return {'file':path.name,'rows':len(rows),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

