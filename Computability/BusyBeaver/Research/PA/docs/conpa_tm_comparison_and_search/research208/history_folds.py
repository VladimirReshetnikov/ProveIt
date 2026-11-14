"""Exact backwards finite-history cubes, including engine states."""
import sys,itertools,json
from pathlib import Path
from collections import defaultdict
sys.path.insert(0,str(Path(__file__).resolve().parent/'pa_tm_research_2026-11-13/pa_tm_research_2026-11-13/work/optimize196'))
import core
rows,labels=core.machine();incoming=defaultdict(list)
for (q,b),(w,d,t) in rows.items(): incoming[t].append((q,b,w,1 if d else -1))

def contexts(q,b,depth=8):
    ans=set()
    def rec(q,h,t,cur,n):
        if not n:
            ans.add(tuple(sorted(cur.items())));return
        for p,a,w,d in incoming[q]:
            hp=h-d
            if hp in t and t[hp]!=w:continue
            cc=cur if hp in t else {**cur,hp:w}
            rec(p,hp,{**t,hp:a},cc,n-1)
    rec(q,0,{0:b},{0:b},depth)
    return [dict(c) for c in ans]

def branchrun(q,h,t,n=64):
    out=[]
    for i in range(n):
        out.append((q,h,tuple(sorted(t.items()))))
        if h not in t:return out, ('unknown',q,h,t)
        a=rows.get((q,t[h]))
        if a is None:return out,None
        w,d,q=a;t=dict(t);t[h]=w;h+=1 if d else -1
    return out, ('limit',q,h,t)

def matches(q,alias,ctx,depth=0):
    aa,ax=branchrun(q,0,ctx)
    bb,bx=branchrun(alias,0,ctx)
    if set(aa[1:]) & set(bb[1:]):return True
    if depth>=6:return False
    if any(x and x[0]=='limit' for x in [ax,bx]):return False
    news=[x[2] for x in [ax,bx] if x and x[0]=='unknown']
    if not news:return False
    p=min(news,key=abs)
    return all(matches(q,alias,{**ctx,p:b},depth+1) for b in (0,1))

def main():
    allctx={}
    for q in labels[:-1]:
        for b in (0,1):allctx[q,b]=contexts(q,b)
    print('contexts',sum(map(len,allctx.values())),flush=True)
    out={f'{q}/{b}':cs for (q,b),cs in allctx.items()}
    (Path(__file__).resolve().parent/'history_contexts.json').write_text(json.dumps(out,indent=1)+'\n')
    for q in sorted(core.BOXSTATES):
        cs=allctx[q,0]+allctx[q,1]
        aliases=[r for r in labels[:-1] if r!=q and all(matches(q,r,c) for c in cs)]
        print(q,'contextcounts',[len(allctx[q,b]) for b in (0,1)],'aliases',aliases,flush=True)
if __name__=='__main__':main()
