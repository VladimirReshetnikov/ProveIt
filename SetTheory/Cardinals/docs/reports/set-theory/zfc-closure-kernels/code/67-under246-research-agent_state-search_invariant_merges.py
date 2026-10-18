#!/usr/bin/env python3
"""State quotient search restricted by the checked register-CFG invariant."""
import sys,json,time,random
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from check_merges_symbolic import BASE,affine,build,cases

class Recording(dict):
    def __init__(self,d):super().__init__(d);self.visited=set()
    def __getitem__(self,k):self.visited.add(k);return super().__getitem__(k)

def live_cases():
    inv=json.loads((HERE.parent/'agent_logic/abstract_k8.json').read_text())
    dead={inv['source_sites'][i][0] for i in inv['dead_leaves']}
    impossible={v['path'] for v in inv['impossible_decrement_cases'] if v['impossible']=='positive'}
    return [c for c in cases() if c[0] not in dead and not (c[0] in impossible and c[1][1] is False)]

def main():
    began=time.monotonic()
    T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in build.build().items()}
    CC=live_cases();random.Random(871).shuffle(CC)
    rec=Recording(T);bykey={k:[] for k in T};byq={q:[] for q,b in T}
    for i,c in enumerate(CC):
        rec.visited.clear();affine.run(rec,*c[:3],halt=c[3],fuel=1200)
        for k in rec.visited:bykey[k].append(i)
        for q in {q for q,b in rec.visited}:byq[q].append(i)
    Q=sorted(byq,key=int)
    print('cases',len(CC),'states observed',sum(bool(v) for v in byq.values()),'missing',[q for q,v in byq.items() if not v],flush=True)
    result={};checks=0;tested=0
    for mode in ('direct','blend'):
      survivors=[]
      for q in Q:
        if q=='96' or not byq[q]:continue
        for r in Q:
            if q==r or not byq[r]:continue
            if mode=='blend' and (T[q,0]==T[r,0] or T[q,1]==T[r,1]):continue
            D={(a,b):(w,d,r if t==q else t) for (a,b),(w,d,t) in T.items() if a!=q}
            if mode=='blend':
                w,d,t=T[q,0];D[r,0]=(w,d,r if t==q else t)
                inds=list(dict.fromkeys(bykey[q,1][:1]+bykey[r,0][:1]+byq[q]+byq[r]))
            else:inds=byq[q]
            tested+=1
            try:
                for i in inds:
                    c=CC[i];affine.run(D,*c[:3],halt=c[3],fuel=1200);checks+=1
            except (AssertionError,KeyError):pass
            else:
                survivors.append((q,r));print('PASS',mode,q,r,'cases',len(inds),flush=True)
            if tested%10000==0:print('progress',mode,tested,'checks',checks,'survivors',len(survivors),'seconds',time.monotonic()-began,flush=True)
      result[mode]=survivors
      (HERE/'invariant_merge_survivors.json').write_text(json.dumps(result,indent=2))
      print('DONE',mode,tested,'checks',checks,'survivors',survivors,'seconds',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
