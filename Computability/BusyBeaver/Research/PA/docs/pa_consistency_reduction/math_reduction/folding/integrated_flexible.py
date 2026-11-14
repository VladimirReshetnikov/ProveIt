#!/usr/bin/env python3
"""Integrated gate with unfolded context-sensitive atom roots when needed."""
from pathlib import Path
import functools,json
import integrated_gate as G
O=G.O
RIGHT_CHILD={'node51':'node50','node14':'node13','node68':'node50','node142':'node40','node147':'node18'}

def make(t,pruned=True):
    m=O.BASE.copy();new={}
    def fresh(key,row0,row1):
        if key in new:return new[key]
        q=1000+len(new);new[key]=q;m[q,0]=row0;m[q,1]=row1
        return q
    def emit(x,bit):
        if x in O.FREE and bit in O.TAGS[x]:return O.FREE[x]
        if isinstance(x,str):
            if x in O.TAGS and bit not in O.TAGS[x]:
                if x not in RIGHT_CHILD:raise ValueError(('unsupported contextual atom',x,bit))
                q=O.ATOMS[x];assert m[q,0][:2]==(0,1)
                return fresh(('unfold',x),m[q,0],(1,1,O.NM[RIGHT_CHILD[x]][0]))
            return O.ATOMS[x]
        if x in new:return new[x]
        def row(y,b):return (0,-1,131 if b else 5)if y=='B' else(b,1,emit(y,b))
        a,b=x;z0=row(a,0);z1=row(b,1);return fresh(x,z0,z1)
    en=emit(t,1);m[89,1]=(1,1,en)
    return(O.prune(m)if pruned else m),new,en
O.make=make

def extra(t):
    z=O.zero_shape(t)[1]
    return 0 if z<=6 else z-5
@functools.lru_cache(maxsize=512)
def evaluate(t):
    if O.zero_shape(t)[1]>8:return 1000,0,0,()
    try:m,ns,en=make(t)
    except ValueError:return 1000,0,0,()
    pro={q for q,b in O.S.ENGINE_ROWS}|{m[k][2]for k in O.S.ENGINE_ROWS if k in m}|{0,O.S.ROOT}
    opts=O.F.candidates(m,{q for q,b in m if q not in pro});sel,tested=O.F.best_subset(m,opts)
    return len(m)//2-len(sel)+extra(t),len(m)//2,len(sel),tuple(sel)
O.evaluate=evaluate

def check(t,path):
    m,ns,en=make(t);score,n,c,sel=evaluate(t);ne=extra(t)
    if ne:
        m[34,0]=(0,-1,2000)
        for j in range(ne):m[2000+j,0]=(0,1,69)if j==ne-1 else(0,-1,2001+j);m[2000+j,1]=(1,-1,3)
    mm,mu=O.F.fold(m,sel);tr=O.C.replace(O.ROOT,O.RAW['x67'],O.raw(t));sites=O.S.flatten(tr)
    old=O.S.all_sites;O.S.all_sites=lambda:sites;fail=[];lens=[]
    try:
        assert O.S.check_engine(mm)
        for i,b,br,s,tar in O.S.contracts():
            v=O.S.execute(mm,br,s,tar)
            if v is None:fail.append((i,b))
            else:lens.append(v[0])
    finally:O.S.all_sites=old
    result=dict(states=len(mm)//2,sites=len(sites),extra_scanner=ne,max_path=max(len(p)for p,op in sites),passed=len(lens),failures=fail,max_symbolic=max(lens,default=0))
    path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(mm.items())))
    path.with_suffix('.check.json').write_text(json.dumps(result,indent=2));path.with_suffix('.sites.json').write_text(json.dumps(sites))
    return result
G.check=check
if __name__=='__main__':G.main()
