#!/usr/bin/env python3
"""Eliminate startup state 5 and search all four output/move choices on 49/1.
Existing states supply the new target. Unlike direct folding, the predecessor
may write a different bit and/or move left. Runtime semantics are checked
from every published instruction site, with register boxes kept unchanged.
"""
from pathlib import Path
from collections import defaultdict
import json,time
from context_search import executor,cases,program_sites,check
from analyze_table import parse_table
ROOT=Path(__file__).parent
base,*_=parse_table(ROOT/'sources/zfc_254.tm');base.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
T={(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in base.items() if q not in (5,8)}
# Baseline already contains the runtime reduction 5 -> 64.
T['49',1]=(0,'R','64')
seen=defaultdict(set);current=[0]
class Tracking(dict):
 def __getitem__(self,k):seen[k].add(current[0]);return super().__getitem__(k)
ns=executor(Tracking(T),ROOT/'sources/symexec.py');cs=cases(ns,program_sites(ROOT/'sources/Prog254.v'))
for j,c in enumerate(cs):current[0]=j;assert check(ns,c)
witnesses=sorted(seen['49',1],key=lambda j:len(cs[j][1]));states=sorted({q for q,b in T},key=int)
result={'tested':0,'runtime_survivors':[],'changed_entry':['49',1],'deleted_states':[5,8],'working_states':252,'scope':'Complete predecessor-action search with 8391 symbolic cases per survivor; no blank startup certificate yet.'}
start=time.monotonic()
for p in states:
 for w in (0,1):
  for d in ('L','R'):
   changed=T.copy();changed['49',1]=(w,d,p);ns['T']=changed;result['tested']+=1
   if all(check(ns,cs[j],fuel=500) for j in witnesses):
    assert all(check(ns,c,fuel=500) for c in cs)
    result['runtime_survivors'].append([w,d,p]);print('SURVIVOR',w,d,p,flush=True)
result['elapsed']=time.monotonic()-start
(ROOT/'startup_extension_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
