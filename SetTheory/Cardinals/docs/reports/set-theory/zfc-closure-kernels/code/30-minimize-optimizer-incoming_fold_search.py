#!/usr/bin/env python3
"""Context split state elimination: independently reroute incoming edges.
Distinct predecessors may use different existing replacement states. This
explores replacements beyond a common target, using a conservative filter
that first requires each replacement to pass independently. Original register-box
contracts are preserved literally; all candidate full tables are rechecked.
"""
from pathlib import Path
from collections import defaultdict
from itertools import product
import json,time
from context_search import executor,cases,program_sites,check
from analyze_table import parse_table
ROOT=Path(__file__).parent
base,*_=parse_table(ROOT/'sources/zfc_254.tm');base.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
T={(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in base.items() if q!=8}
seen=defaultdict(set);current=[0]
class Tracking(dict):
 def __getitem__(self,k):seen[k].add(current[0]);return super().__getitem__(k)
ns=executor(Tracking(T),ROOT/'sources/symexec.py');cs=cases(ns,program_sites(ROOT/'sources/Prog254.v'))
for j,c in enumerate(cs):current[0]=j;assert check(ns,c)
order=sorted(range(len(cs)),key=lambda j:len(cs[j][1]));rank={j:r for r,j in enumerate(order)}
boxstates={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
protected={(str(q),b) for q in boxstates for b in (0,1)}-{('3',0)}
core=boxstates|{96,5}
states=sorted({q for q,b in T},key=int)
incoming=defaultdict(list)
for pair,(_,_,q) in T.items():
 if q!=pair[0]:incoming[q].append(pair)
eligible=[q for q in states if int(q) not in core and len(incoming[q])>1 and not any(pair in protected for pair in incoming[q])]
result={'scope':'Predecessor-specific replacements under unchanged box contracts; bounded affine executor, no kernel proof.',
 'eligible_states':eligible,'tested_single_edge_candidates':0,'single_edge_options':{},'elimination_candidates':0,'runtime_survivors':[]}
start=time.monotonic()
for qi,q in enumerate(eligible):
 options=[];impossible=False
 pairs=sorted(incoming[q],key=lambda p:len(seen[p]))
 for pair in pairs:
  good=[];w,d,_=T[pair];witnesses=sorted(seen[pair],key=rank.get)
  for p in states:
   if p==q:continue
   changed=T.copy();changed[pair]=(w,d,p);ns['T']=changed;result['tested_single_edge_candidates']+=1
   if all(check(ns,cs[j],fuel=500) for j in witnesses):good.append(p)
  result['single_edge_options'][str(pair)]={'original_target':q,'alternatives':good}
  options.append((pair,good))
  if not good:impossible=True;break
 if not impossible:
  total=1
  for _,good in options:total*=len(good)
  print('ALL EDGE OPTIONS',q,'combinations',total,flush=True)
  if total<=10000:
   for chosen in product(*(good for _,good in options)):
    changed={k:v for k,v in T.items() if k[0]!=q}
    for (pair,_),p in zip(options,chosen):w,d,_=T[pair];changed[pair]=(w,d,p)
    ns['T']=changed;result['elimination_candidates']+=1
    if all(check(ns,cs[j],fuel=500) for j in order):
     survivor={'deleted':q,'redirects':[[list(pair),p] for (pair,_),p in zip(options,chosen)]}
     result['runtime_survivors'].append(survivor);print('SURVIVOR',survivor,flush=True)
 result['elapsed']=time.monotonic()-start
 if qi%5==0 or not impossible:
  (ROOT/'incoming_fold_results.json').write_text(json.dumps(result,indent=2)+'\n')
  print('progress',qi,'/',len(eligible),'candidates',result['tested_single_edge_candidates'],'secs',round(result['elapsed'],1),flush=True)
result['elapsed']=time.monotonic()-start
(ROOT/'incoming_fold_results.json').write_text(json.dumps(result,indent=2)+'\n')
print('DONE',len(result['runtime_survivors']),'survivors',result['tested_single_edge_candidates'],'tried',result['elapsed'],'secs',flush=True)
