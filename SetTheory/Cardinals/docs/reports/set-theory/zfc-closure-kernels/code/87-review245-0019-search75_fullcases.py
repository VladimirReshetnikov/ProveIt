"""Self-authored finite whole-instruction filter; no downloaded code imports."""
from pathlib import Path
import os
if not __debug__: raise RuntimeError("Assertions must remain enabled")
import sys,json,time
import independent_runtime as r
P=Path(os.environ.get('B245_OUTPUT',Path(__file__).resolve().parent.parent/'results'));t=r.table(P/'candidates/candidate_appendzero244_old.tm');states=sorted({q for q,b in t});ss=r.sites(json.loads((r.BASE/'candidate-routing245/grammar.json').read_text()));zero=next(s for s in ss if s[1]=='CD');ci=next(s for s in ss if s[1]=='CI');cases=[(zero,[0]*9,[1]),(zero,[0 if i==zero[2]else 2 for i in range(9)],[2,0,1]),(ci,[0]*9,[0])]
hits=[];staged=[0]*len(cases);began=time.time()
for q in states:
 for w in[0,1]:
  for d in[-1,1]:
   u=t.copy();u[75,0]=(w,d,q);okay=True
   for i,(site,regs,spares)in enumerate(cases):
    actual,steps,_=r.run(u,site[0],regs,spares,limit=12000)
    want=r.expected(site,regs,spares)
    allowed=[want[0]]
    if site[1]=='CI':
     # Alternate sparevalues0..3, retain required logical effect/pointer/head.
     nregs=regs.copy();nregs[site[2]]+=1;pc,shift=r.inc(site[0]);allowed=[(96,-shift,{v-shift for v in r.frame(pc,nregs,spares+[z],shift)})for z in range(4)]
    if actual not in allowed:okay=False;break
    staged[i]+=1
    if i==1:print("CD survivor",w,d,q,flush=True)
   if okay:hits.append({'row':(w,d,q)})
res={'scope':'Finite 3-case filter, 12000steps percase, CI spare0..3 allowed','rows':len(states)*4,'pass_counts':staged,'hits':hits,'seconds':time.time()-began,'cases':cases};(P/'retarget75_fullcases.json').write_text(json.dumps(res,indent=2)+'\n');print(res)
