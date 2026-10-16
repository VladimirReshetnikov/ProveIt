#!/usr/bin/env python3
"""Find single-row runtime-preserving extensions of the prepared 252 core.
All output bits, directions, and existing targets are tried outside the fixed
register-box contracts. Only baseline cases reading a changed entry need be
rerun: every other case has exactly the same deterministic execution.
"""
from pathlib import Path
from collections import defaultdict
import json,time
from context_search import executor,cases,program_sites,check
from analyze_table import parse_table
ROOT=Path(__file__).parent
base,*_=parse_table(ROOT/'sources/zfc_254.tm');base.update({(3,0):(0,'L',48)})
T={(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in base.items() if q not in (5,8)}
seen=defaultdict(set);current=[0]
class Tracking(dict):
 def __getitem__(self,k):seen[k].add(current[0]);return super().__getitem__(k)
ns=executor(Tracking(T),ROOT/'sources/symexec.py');cs=cases(ns,program_sites(ROOT/'sources/Prog254.v'))
for j,c in enumerate(cs):current[0]=j;assert check(ns,c)
rank={j:r for r,j in enumerate(sorted(range(len(cs)),key=lambda j:len(cs[j][1])))}
boxstates={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
protected={(str(q),b) for q in boxstates for b in (0,1)}-{('3',0)}
eligible=sorted(set(T)-protected,key=lambda p:(int(p[0]),p[1]))
states=sorted({q for q,b in T}|{'254'},key=int)
result={'scope':'Single-transition changes of prepared252 preserving all 8391 affine sites and fixed boxes; no kernel proof or blank startup certificate.',
 'eligible_pairs':len(eligible),'targets':len(states),'tested':0,'survivors':[]}
start=time.monotonic()
for ki,pair in enumerate(eligible):
 witnesses=sorted(seen[pair],key=rank.get)
 assert witnesses,pair
 changed=T.copy();ns['T']=changed
 for q in states:
  for w in (0,1):
   for d in ('L','R'):
    row=(w,d,q)
    if row==T[pair]:continue
    changed[pair]=row;result['tested']+=1
    if all(check(ns,cs[j],fuel=500) for j in witnesses):
     result['survivors'].append([int(pair[0]),pair[1],w,d,int(q)])
 if ki%10==0:
  result['elapsed']=time.monotonic()-start
  (ROOT/'single_row_results.json').write_text(json.dumps(result,indent=2)+'\n')
  print('progress',ki,'/',len(eligible),'tested',result['tested'],'survivors',len(result['survivors']),'secs',round(result['elapsed'],1),flush=True)
result['elapsed']=time.monotonic()-start
(ROOT/'single_row_results.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'single_row_survivors.tsv').write_text(''.join(' '.join(map(str,x))+'\n' for x in result['survivors']))
print('DONE',result['tested'],'tests',len(result['survivors']),'survivors',result['elapsed'],'secs',flush=True)
