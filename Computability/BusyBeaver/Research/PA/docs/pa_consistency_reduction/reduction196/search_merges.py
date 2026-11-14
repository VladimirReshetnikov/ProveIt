from pathlib import Path
from itertools import combinations
from collections import deque

def contexts(m,r=3):
    W=2*r+1;mask=(1<<W)-1
    todo=deque([(0,0)]);seen={(0,0)};out={q:set() for q,b in m}
    while todo:
        q,t=todo.popleft()
        if q not in out:continue
        out[q].add(t)
        b=(t>>r)&1;w,d,n=m[q,b]
        u=(t&~(1<<r))|(w<<r)
        vs=(u>>1,(u>>1)|(1<<(W-1))) if d=='R' else ((u<<1)&mask,((u<<1)|1)&mask)
        for v in vs:
            if (n,v) not in seen:seen.add((n,v));todo.append((n,v))
    return out

def load(path):
    m={}
    for l in Path(path).read_text().splitlines():
        q,b,w,d,n=l.split();m[int(q),int(b)]=(int(w),d,int(n))
    return m

def search(m,r=3):
    qs=sorted(set(q for q,b in m))
    incoming={q:[] for q in qs}
    for (q,b),(w,d,n) in m.items():
        if n in incoming:incoming[n].append((q,b,w,d))
    # Strong all-configuration predecessor-bit conditions.
    ctx=contexts(m,r)
    bit={}
    for q in qs:
        for b in range(2):
            v={(x>>(r-1))&1 for x in ctx[q] if ((x>>r)&1)==b}
            if len(v)==1:bit[q,b]=next(iter(v))
    pure=[q for q in qs if all(m[q,b][:2]==(b,'R') for b in range(2))]
    out=[]
    for q,r in combinations(pure,2):
        opts=[]
        for b in range(2):
            if m[q,b]==m[r,b]:opts.append([('same',m[q,b])]);continue
            if (q,b) not in bit or (r,b) not in bit or bit[q,b]==bit[r,b]:opts.append([]);continue
            cs=[]
            for s in pure:
                if s in (q,r):continue
                t=m[s,bit[q,b]][2];u=m[s,bit[r,b]][2]
                if t not in(q,r) and u not in(q,r) and m.get((t,b))==m[q,b] and m.get((u,b))==m[r,b]:
                    cs.append(('back',s))
            opts.append(cs)
        if all(opts):out.append((q,r,[bit.get((q,b)) for b in range(2)],[bit.get((r,b)) for b in range(2)],opts))
    return out

if __name__=='__main__':
    m=load(Path(__file__).with_name('pa196.tm'))
    import sys
    radius=int(sys.argv[1]) if len(sys.argv)>1 else 3
    for z in search(m,radius):print(z)
