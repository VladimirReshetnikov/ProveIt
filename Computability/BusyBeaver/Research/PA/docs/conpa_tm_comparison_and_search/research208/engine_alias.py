"""Bounded exact local alias search on specified partial-tape contexts."""
from pathlib import Path
import sys,itertools,json
sys.path.insert(0,str(Path(__file__).resolve().parent/'pa_tm_research_2026-11-13/pa_tm_research_2026-11-13/work/optimize196'))
import core
rows,labels=core.machine()

def branchrun(q,h,t,n=100):
    out=[]
    for i in range(n):
        out.append((q,h,tuple(sorted(t.items()))))
        if h not in t:return out, ('unknown',q,h,t)
        a=rows.get((q,t[h]))
        if a is None:return out,None
        w,d,q=a;t=dict(t);t[h]=w;h+=1 if d else -1
    return out, ('limit',q,h,t)

def matches(q,alias,ctx,depth=0):
    # Both runs branch on every newly inspected symbolic tape cell.
    aa,ax=branchrun(q,0,ctx)
    bb,bx=branchrun(alias,0,ctx)
    if set(aa[1:]) & set(bb[1:]):return True
    if depth>=8:return False
    if any(x and x[0]=='limit' for x in [ax,bx]):return False
    news=[x[2] for x in [ax,bx] if x and x[0]=='unknown']
    if not news:return False
    p=min(news,key=abs)
    return all(matches(q,alias,{**ctx,p:b},depth+1) for b in (0,1))

def main():
    for q,contexts in [(198,[{-3:1,-2:0,-1:1,0:b} for b in (0,1)]),
                       (66,[{-2:1,-1:0,0:b} for b in (0,1)]),
                       (16,[{-1:0,0:b} for b in (0,1)]),
                       (94,[{-1:1,0:b} for b in (0,1)]),
                       (74,[{-1:0,0:b} for b in (0,1)])]:
        hit=[]
        for r in labels[:-1]:
            if r==q:continue
            if all(matches(q,r,c) for c in contexts):hit.append(r)
        print(q,hit,flush=True)
if __name__=='__main__': main()
