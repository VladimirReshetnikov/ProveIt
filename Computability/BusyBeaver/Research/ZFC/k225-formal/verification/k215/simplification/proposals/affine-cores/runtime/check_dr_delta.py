
if not __debug__:
    raise RuntimeError("Verification requires enabled assertions; do not use python -O or PYTHONOPTIMIZE.")

from pathlib import Path
import sys,json
D=Path(__file__).parent;R=D.parent
import analyze_symbolic as A
old=A.I.table(D/'inputs/ST215.tm');new=A.I.table(D/'inputs/DR215.tm');changes={k for k in old if old[k]!=new[k]};assert set(old)==set(new)
s0=json.load(open(D/'inputs/ST215.sites.json'));s1=json.load(open(D/'inputs/DR215.sites.json'));assert len(s0)==len(s1)
source_delta=[i for i in range(len(s0))if s0[i]!=s1[i]];hit=[];newchecks=[];guards=0
for i,site in enumerate(s0):
 for pos in([False,True]if site[1]=='CD'else[False]):
  tr,states,_,_=A.run(old,site,pos);guards+=1;used=set()
  for ev,bs in zip(tr,states):
   br,st=bs;q,on,l,r=st
   if ev[0]=='literal':used.add((q,r[0][1]))
   elif ev[0]in('scan','peel'):
    a=(l if on else r)[0];used.add((q,a[1]))
   elif ev[0]=='boxedge':used.add((q,0))
  if used&changes:
   hit.append(dict(index=i,positive=pos,rows=sorted(used&changes),source_changed=i in source_delta))
   tr2,_,_,_=A.run(new,s1[i],pos);newchecks.append(dict(index=i,positive=pos,steps=len(tr2)))
out=dict(changed_rows=sorted(changes),changed_source_ordinals=source_delta,total_guards=guards,affected_guard_count=len(hit),affected_guards=hit,changed_cases_pass=newchecks,unaffected_guard_count=guards-len(hit),scope='Owned Lean-rule transcription with BoxLemmas assumed. Literal-row dependency audit; engine box theorem footprint must be separately shown disjoint from patch before formal transport.')
(D/'DR_DELTA.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
