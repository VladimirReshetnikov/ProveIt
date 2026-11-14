"""Search contextual mergers involving protected register-engine states.

This is bounded exploration, never a correctness claim by itself.
"""
from pathlib import Path
import sys,itertools,json,time
from collections import defaultdict
import history_folds as h
rows,labels=h.rows,h.labels
raw=json.loads((Path(__file__).resolve().parent/'history_contexts.json').read_text())
cs={tuple(map(int,k.split('/'))):[{int(p):b for p,b in c.items()} for c in v]for k,v in raw.items()}
FUEL=100
def run(m,q,t):
    heads=[];pos=0
    for n in range(FUEL):
        heads.append((q,pos,tuple(sorted(t.items()))))
        if pos not in t:return heads,pos
        tr=m.get((q,t[pos]))
        if tr is None:return heads,None
        w,d,q=tr;t={**t,pos:w};pos+=1 if d else -1
    return heads,None
def match(m,q,r,c,a,b,depth=0):
    aa,unknowna=run(rows,q,c)
    bb,unknownb=run(m,r,c)
    if set((b if q==a else q,p,t) for q,p,t in aa[1:]) & set(bb[1:]):return True
    if depth>=7:return False
    unks=[u for u in (unknowna,unknownb) if u is not None]
    if not unks:return False
    p=min(unks,key=abs)
    return all(match(m,q,r,{**c,p:v},a,b,depth+1) for v in (0,1))

def main():
    pairs=[]
    for a,b in itertools.combinations(labels[:-1],2):
        if not {a,b}&h.core.BOXSTATES:continue
        common=[bit for bit in (0,1) if rows[a,bit]==rows[b,bit]]
        if len(common)==1:pairs.append((a,b,1-common[0]))
    print('pairs',len(pairs),pairs,flush=True)
    t0=time.time();tested=0
    for a,b,bit in pairs:
        base={(q,x):(w,d,b if tgt==a else tgt) for (q,x),(w,d,tgt) in rows.items() if q!=a}
        full=[(src,c) for src in(a,b) for c in cs[src,bit]]
        # Shortest cubes expose missing guards first.
        full.sort(key=lambda x:len(x[1]))
        seen=0
        for w,d,tgt in itertools.product((0,1),(False,True),labels):
            if tgt==a:continue
            base[b,bit]=(w,d,tgt);tested+=1
            if all(match(base,src,b,c,a,b) for src,c in full):
                print('FOUND',a,b,bit,(w,d,tgt),flush=True)
                dest=Path(__file__).resolve().parent/f'merge_{a}_{b}.json'
                dest.write_text(json.dumps({'remove':a,'retain':b,'bit':bit,'new':(w,d,tgt),'rows':[[q,x,*tr]for(q,x),tr in sorted(base.items())]},indent=2)+'\n')
                seen+=1
        print('done',a,b,'hits',seen,'tested',tested,'seconds',time.time()-t0,flush=True)
if __name__=='__main__':main()
