#!/usr/bin/env python3
"""Screen directed folds with the inherited universal affine checker."""
import sys,json,time,random
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'sources/context246/zfc-context246'
sys.path.insert(0,str(BASE/'code'))
sys.path.insert(0,str(BASE/'sources/prior'))
import prefix_affine as affine
import rebuild_machines as build
import review_affine_source as audit

class Recording(dict):
    def __init__(self,d):super().__init__(d);self.visited=set()
    def __getitem__(self,k):self.visited.add(int(k[0]));return super().__getitem__(k)

def cases():
    _,sites=audit.parse_source(BASE/'sources/Prog254.v')
    for p,op,r in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(r,zero) if op=='CD' else None
            extra,effect,overflow=0,None,False
            if op=='CI':
                successor,overflow=audit.full_inc(p);effect=('inc',r)
            elif op=='CD' and not zero:
                successor,overflow=audit.full_inc(p);effect=('dec',r);extra=1
            elif op=='CD':successor,overflow=audit.full_inc(audit.full_strip(p,'0',1))
            elif op=='CB':successor,overflow=audit.full_inc(audit.full_strip(p,'0',r))
            elif op=='CC':successor=audit.full_strip(p,'1',r)
            else:successor=''
            right=[('b',int(b)) for b in successor]+[('r',0,1,40+extra+int(overflow)-len(successor)),('b',1),('box',('plain',effect))]
            yield (p,branch,affine.canon([('b',1)],right),op=='CH')

def main():
    began=time.monotonic()
    T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in build.build().items()}
    CC=list(cases());random.Random(871).shuffle(CC)
    rec=Recording(T);byq={q:[] for q,b in build.build()}
    for c in CC:
        rec.visited.clear();affine.run(rec,*c[:3],halt=c[3],fuel=1200)
        for q in rec.visited:byq[q].append(c)
    pairs=json.loads((HERE/'merge_candidates.json').read_text())
    print('symbolic starting',len(pairs),'seconds',time.monotonic()-began,flush=True)
    survivors=[];checks=0
    for i,(q,r) in enumerate(pairs):
        D={(a,b):(w,d,str(r) if t==str(q) else t) for (a,b),(w,d,t) in T.items() if a!=str(q)}
        try:
            for c in byq[q]:affine.run(D,*c[:3],halt=c[3],fuel=1200);checks+=1
        except (AssertionError,KeyError):pass
        else:
            survivors.append((q,r));print('PASS',q,r,'cases',len(byq[q]),flush=True)
        if i%100==0:print('progress',i,'survivors',len(survivors),'checks',checks,'seconds',time.monotonic()-began,flush=True)
    (HERE/'symbolic_merge_survivors.json').write_text(json.dumps(survivors,indent=2))
    print(survivors,flush=True)

if __name__=='__main__':main()
