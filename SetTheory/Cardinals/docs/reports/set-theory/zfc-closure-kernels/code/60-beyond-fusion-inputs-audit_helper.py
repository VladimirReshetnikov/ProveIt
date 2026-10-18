#!/usr/bin/env python3
"""Minimal unmodified function/constant excerpts from the pinned ProveIt audit.
See sources.json for provenance. No source-root lookup or CLI dependency.
"""
from collections import Counter

PERM=(0,3,4,5,8,1,6,2,7)

PHYS=(6,7,0,2,1,8,4,3,5)

NEWPHYS=tuple(PERM[r] for r in PHYS)

SKIP=(60,44,31,56,38,40,28,64,69)

SELECTOR_INCOMING={(169,1),(173,1),(18,1),(201,1),(21,1),(25,1),(39,1),
                   (47,1),(49,1),(53,1),(65,1),(70,1),(72,1),(93,1)}

BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}

BOX_PAIRS={(q,b) for q in BOX_STATES for b in (0,1)}-{(3,0)}

EXPECTED_SHA='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'

def read_table(data):
    rows={}
    for line in data.decode().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();key=int(q),int(b)
            assert key not in rows
            rows[key]=int(w),d,int(t)
    return rows

def increment(p):
    bits=list(p)
    while bits and bits[-1]=='1':bits.pop()
    return ''.join(bits[:-1])+ '1' if bits else None

def strip(p,bit,n):
    i=len(p)
    while n and i:
        i-=1;n-=p[i]==bit
    return p[:i]

def successor(p,op,r,zero):
    if op=='CI' or op=='CD' and not zero:return increment(p)
    if op=='CD':return increment(strip(p,'0',1))
    if op=='CB':return increment(strip(p,'0',r))
    if op=='CC':return strip(p,'1',r)
    return ''

def paint(pc,gap,registers,spares,head):
    assert len(pc)<=gap
    ones={head-1,head+gap}|{head+i for i,b in enumerate(pc) if b=='1'}
    cursor=head+gap+1
    for value in registers+spares:
        cursor+=1;ones.update(range(cursor,cursor+value+1));cursor+=value+1
    return ones

def run_prefix(table,n):
    q=64;head=0;ones=set();used=Counter();prefix9=None
    for i in range(n):
        assert q!=254,('unexpected_prefix_halt',i)
        key=q,int(head in ones);used[key]+=1;w,d,q=table[key]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
        if i==8:prefix9={'state':q,'head':head,'ones':sorted(ones)}
    return q,head,ones,used,prefix9
