#!/usr/bin/env python3
from pathlib import Path
import importlib.util,json,time
from collections import Counter
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent/'source'
spec=importlib.util.spec_from_file_location('lit',ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/63-context246-code-check_literal_instructions.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
T=c.read_table(ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm')
P=ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
seen=Counter();bad=[];cases=0;t0=time.monotonic()
for pc,op,r in c.program_sites(P):
 for positive in ((False,True) if op=='CD' else (None,)):
  regs=[0]*9
  if positive:regs[c.PHYSICAL[r]]=1
  target=c.expected(pc,op,r,regs,[1],0,40)
  q,h,ones=96,0,c.paint(pc,40,regs,[1],0);events=[]
  for step in range(20000):
   if q==48 and h not in ones:
    l=int(h-1 in ones);seen[op+str(positive)+str(l)]+=1
    if l:events.append((step,h,h-len(pc)))
   w,d,q=T[q,int(h in ones)]
   if w:ones.add(h)
   else:ones.discard(h)
   h+=d
   if q==254:
    assert op=='CH';break
   if q==96 and target and (h,ones)==target[:2]:break
  else:raise AssertionError((pc,op,r,positive))
  if events:bad.append(dict(pc=pc,operation=op,r=r,positive=positive,events=events))
  cases+=1
out=dict(scope='Complete guarded source-site census on one concrete register fixture per guard, not universal runtime proof',cases=cases,events=dict(seen),bad_case_count=len(bad),bad_by_operation=dict(Counter(x['operation'] for x in bad)),bad=bad,seconds=time.monotonic()-t0)
(HERE/'return_context_census.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='bad'},indent=2))
