#!/usr/bin/env python3
"""Finite window abstraction, sound for arbitrary tape outside the window."""
from pathlib import Path
from collections import deque, defaultdict
import argparse,json,itertools

def read(p):
    T={}; start=0
    for line in Path(p).read_text().splitlines():
        if line.startswith('#! start '):start=int(line[9:])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    return T,start

def analyze(T,start,r,blank):
    states=sorted({q for q,b in T}); W=2*r+1; B=1<<W; mask=B-1
    seen={q:bytearray(B) for q in states}; work=deque()
    for m in ([0] if blank else range(B)):
        seen[start][m]=1;work.append((start,m))
    n=0
    while work:
        q,m=work.popleft();n+=1
        b=(m>>r)&1; w,d,t=T[q,b]
        if t not in seen:continue
        x=(m&~(1<<r))|(w<<r)
        a=x>>1 if d==1 else ((x<<1)&mask)
        c=a|(1<<(W-1)) if d==1 else a|1
        for y in (a,c):
            if not seen[t][y]:seen[t][y]=1;work.append((t,y))
    local={q:sorted({(m>>(r-1))&7 for m in range(B) if seen[q][m]}) for q in states}
    unreachable=[]; pairs=[]
    for q in states:
        for b in (0,1):
            if not any((a>>1)&1==b for a in local[q]):unreachable.append([q,b])
    for p,q in itertools.combinations(states,2):
        for b in (0,1):
            if T[p,1-b]!=T[q,1-b]:continue
            for side in (-1,1):
                bit=0 if side==-1 else 2
                pm={a>>bit&1 for a in local[p] if a>>1&1==b}
                qm={a>>bit&1 for a in local[q] if a>>1&1==b}
                if len(pm)==len(qm)==1 and pm!=qm:
                    pairs.append(dict(p=p,q=q,branch=b,side=side,pmarker=list(pm)[0],qmarker=list(qm)[0],ptransition=T[p,b],qtransition=T[q,b]))
    return dict(radius=r,blank_window=blank,configs=n,local=local,masks={q:[m for m in range(B) if seen[q][m]] for q in states},unreachable_rows=unreachable,distinguishable_pairs=pairs)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('--radius',type=int,default=3);p.add_argument('--blank',action='store_true');p.add_argument('--out',required=True);a=p.parse_args()
    T,start=read(a.table);x=analyze(T,start,a.radius,a.blank);Path(a.out).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items() if k not in ('local','masks')},indent=2))
