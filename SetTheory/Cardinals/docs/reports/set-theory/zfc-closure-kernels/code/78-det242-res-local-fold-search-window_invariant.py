#!/usr/bin/env python3
"""Sound finite tape-window reachability over arbitrary initial tape at state 95.

The window is a finite abstraction: when a cell enters the boundary, both values
are possible. Thus the fixed point proves a universally quantified inductive
invariant, independently of bounded concrete traces.
"""
import sys, json, pickle
from pathlib import Path
from collections import deque, defaultdict

def read_table(path):
    return {(int(q),int(s)):(int(w),1 if d=='R' else -1,int(t))
            for row in Path(path).read_text().splitlines()
            if row and not row.startswith('#')
            for q,s,w,d,t in [row.split()]}

def invariant(table,L,R,start=95,blank=False):
    n=L+R+1; limit=1<<n; mask=limit-1
    reached={q:bytearray(limit) for q,s in table}
    todo=deque()
    for v in ([0] if blank else range(limit)):
        reached[start][v]=1; todo.append((start,v))
    while todo:
        q,v=todo.popleft(); w,d,t=table[q,(v>>L)&1]
        if t not in reached: continue
        u=(v&~(1<<L))|(w<<L)
        if d==1: a=u>>1; b=a|(1<<(n-1))
        else: a=(u<<1)&mask; b=a|1
        arr=reached[t]
        if not arr[a]: arr[a]=1;todo.append((t,a))
        if not arr[b]: arr[b]=1;todo.append((t,b))
    return reached

if __name__=='__main__':
    L=int(sys.argv[1]) if len(sys.argv)>1 else 6
    R=int(sys.argv[2]) if len(sys.argv)>2 else 2
    path=Path(__file__).with_name('base.tm');table=read_table(path)
    reached=invariant(table,L,R)
    out=Path(__file__).with_name(f'invariant_L{L}_R{R}.pkl')
    out.write_bytes(pickle.dumps((L,R,reached)))
    print(json.dumps({'L':L,'R':R,'reached_windows':sum(map(sum,reached.values())),
                      'all_possible':len(reached)*(1<<(L+R+1)),
                      'counts':{q:sum(reached[q]) for q in sorted(reached)}},indent=2))
