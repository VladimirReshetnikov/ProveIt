import math,json,itertools
from functools import lru_cache
from pathlib import Path

def partitions(n,lo=1):
    if n==0: yield (); return
    for k in range(lo,n+1):
        for p in partitions(n-k,k): yield (k,)+p

def setparts(n):
    blocks=[]
    def rec(i):
        if i==n:
            yield tuple(tuple(b) for b in blocks);return
        for b in blocks:
            b.append(i);yield from rec(i+1);b.pop()
        blocks.append([i]);yield from rec(i+1);blocks.pop()
    yield from rec(0)

def invariant_direct(lengths,parts):
    sig=[];start=0
    for l in lengths:
        sig.extend(list(range(start+1,start+l))+[start]);start+=l
    return sum(frozenset(frozenset(sig[i] for i in b) for b in p)==frozenset(map(frozenset,p)) for p in parts)

def cycle_formula(lengths):
    @lru_cache(None)
    def rec(mask):
        if not mask:return 1
        bit=mask&-mask;other=mask^bit;s=other;out=0
        while True:
            block=s|bit;inds=[i for i in range(len(lengths)) if block>>i&1]
            g=math.gcd(*(lengths[i] for i in inds));h=len(inds)
            weight=sum(k**(h-1) for k in range(1,g+1) if g%k==0)
            out+=weight*rec(mask^block)
            if not s:break
            s=(s-1)&other
        return out
    return rec((1<<len(lengths))-1)

B=[len(list(setparts(n))) for n in range(9)]
rows=[];burnside=[]
for n in range(9):
    ps=list(setparts(n));total=0;mass=0
    for p in partitions(n):
        f=invariant_direct(p,ps);g=cycle_formula(p)
        if f!=g:raise ValueError((p,f,g))
        c=len(p);d=n-c
        if not B[c]<=f<=B[c]*math.prod(p)<=B[c]*2**d:raise ValueError(('bound',p))
        denom=math.prod(l**p.count(l)*math.factorial(p.count(l)) for l in set(p))
        count=math.factorial(n)//denom
        total+=count*f*f;mass+=count*B[c]**2
        rows.append({'cycle_type':p,'fixed_partitions':f})
    if total%math.factorial(n):raise ValueError('Burnside not integer')
    burnside.append(total//math.factorial(n))
result={'passed':True,'cycle_types_checked':len(rows),'bell_numbers':B,'A007716_prefix':burnside,'rows':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
