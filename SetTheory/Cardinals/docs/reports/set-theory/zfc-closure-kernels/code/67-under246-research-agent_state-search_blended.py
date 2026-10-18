#!/usr/bin/env python3
"""Search two-state quotients with one row contributed by each state."""
import sys,json,time,random
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from check_merges_symbolic import BASE,affine,build,cases

class Recording(dict):
    def __init__(self,d):super().__init__(d);self.visited=set()
    def __getitem__(self,k):self.visited.add(k);return super().__getitem__(k)

def main():
    began=time.monotonic()
    T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in build.build().items()}
    CC=list(cases());random.Random(871).shuffle(CC)
    rec=Recording(T);bykey={k:[] for k in T};byq={q:[] for q,b in T}
    for i,c in enumerate(CC):
        rec.visited.clear();affine.run(rec,*c[:3],halt=c[3],fuel=1200)
        for k in rec.visited:bykey[k].append(i)
        for q in {q for q,b in rec.visited}:byq[q].append(i)
    Q=sorted(byq,key=int)
    print('states observed',sum(bool(v) for v in byq.values()),'missing',[q for q,v in byq.items() if not v],flush=True)
    # Empty macro traces use axiomatic contracts, so their row changes cannot
    # be established by this search and must be separately proved afterwards.
    survivors=[];checks=0;tested=0
    for q in Q:
        if q=='96' or not byq[q]:continue
        for r in Q:
            if q==r or not byq[r]:continue
            # Keep r; q contributes row0, r contributes row1. The symmetric
            # directed pair considers the complementary mixed assignment.
            if T[q,0]==T[r,0] or T[q,1]==T[r,1]:continue
            D={(a,b):(w,d,r if t==q else t) for (a,b),(w,d,t) in T.items() if a!=q}
            w,d,t=T[q,0];D[r,0]=(w,d,r if t==q else t)
            inds=list(dict.fromkeys(bykey[q,1][:1]+bykey[r,0][:1]+byq[q]+byq[r]))
            tested+=1
            try:
                for i in inds:
                    c=CC[i];affine.run(D,*c[:3],halt=c[3],fuel=1200);checks+=1
            except (AssertionError,KeyError):pass
            else:
                survivors.append((q,r));print('PASS',q,r,'cases',len(inds),flush=True)
            if tested%10000==0:print('progress',tested,'checks',checks,'survivors',len(survivors),'seconds',time.monotonic()-began,flush=True)
    (HERE/'blended_survivors.json').write_text(json.dumps(survivors,indent=2))
    print('DONE',tested,'checks',checks,'survivors',survivors,'seconds',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
