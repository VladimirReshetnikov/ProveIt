"""Locally authored finite smoke test, not a substitute for the theorem."""
from math import isqrt
import json

def pair(a,b):
    s=a+b
    return s*(s+1)//2+b

def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b

def parse(n):
    out=[]
    while True:
        tag,r=unpair(n)
        fields=[tag]
        for _ in range(0 if tag<2 else 1 if tag==2 else 2):
            f,r=unpair(r)
            fields.append(f)
        out.append(tuple(fields))
        if not r: return out
        n=r-1

def encode(word):
    r=0
    for cmd in reversed(word):
        for f in reversed(cmd): r=pair(f,r)
        r+=1
    return r-1

N=100000
seen=set()
balance=minimum=pops=pushes=0
for n in range(N):
    word=parse(n)
    assert encode(word)==n
    for j,cmd in enumerate(word):
        if cmd[0]==0:
            balance+=1; pushes+=1
        elif cmd[0]==1:
            lowered=word[:j]+[(0,)]+word[j+1:]
            m=encode(lowered)
            assert m<n and parse(m)==lowered
            assert (m,j) not in seen
            seen.add((m,j))
            assert balance>0
            balance-=1; pops+=1
        minimum=min(minimum,balance)
report=dict(candidate_count=N,pushes=pushes,pops=pops,
            minimum_prefix_balance=minimum,images=len(seen),
            roundtrips_and_lowering_checks='passed',formal_proof=False)
print(json.dumps(report,indent=2))
