#!/usr/bin/env python3
"""Search mixed transition-row merges beyond ordinary direct redirection.
A pair a,b is replaced by b; the read-0 row is chosen from a and read-1
row from b, or the opposite. Protected register-box rows are unchanged.
Candidates pass all affected affine sites then the full 8,391-case suite.
"""
from pathlib import Path
from collections import defaultdict
import json,time
from context_search import executor,cases,program_sites,check
from analyze_table import parse_table
ROOT=Path(__file__).parent
base,*_=parse_table(ROOT/'sources/zfc_254.tm')
base.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
T={(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in base.items() if q!=8}
ns=executor(T,ROOT/'sources/symexec.py')
cs=cases(ns,program_sites(ROOT/'sources/Prog254.v'))
seen=defaultdict(set);current=[0]
def observe(q,*args):seen[q].add(current[0])
ns['OBSERVE']=observe
for j,c in enumerate(cs):current[0]=j;assert check(ns,c)
ns['OBSERVE']=None
order=sorted(range(len(cs)),key=lambda j:len(cs[j][1]))
rank={j:r for r,j in enumerate(order)}
protected={0,1,2,3,4,5,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131,96}
eligible=[q for q in sorted(seen,key=int) if (q,0) in T and int(q) not in protected]
result={'baseline_cases':len(cs),'eligible_states':len(eligible),'tested':0,'redundant_single_row_equal':0,'survivors':[],'scope':'Mixed-row state merges, unchanged protected box contracts; no kernel proof.'}
start=time.monotonic()
for ai,a in enumerate(eligible):
 for b in eligible[ai+1:]:
  if T[a,0]==T[b,0] or T[a,1]==T[b,1]:result['redundant_single_row_equal']+=2;continue
  witnesses=sorted(seen[a]|seen[b],key=rank.get)
  for branch in (0,1):
   changed={k:(w,d,b if t==a else t) for k,(w,d,t) in T.items() if k[0]!=a}
   w,d,t=T[a,branch];changed[b,branch]=(w,d,b if t==a else t)
   ns['T']=changed;result['tested']+=1
   if all(check(ns,cs[j],fuel=500) for j in witnesses):
    assert all(check(ns,c,fuel=500) for c in cs)
    result['survivors'].append({'deleted':a,'merged_into':b,'row_from_deleted':branch})
    print('SURVIVOR',result['survivors'][-1],flush=True)
 if ai%10==0:
  result['elapsed']=time.monotonic()-start
  (ROOT/'mixed_fold_results.json').write_text(json.dumps(result,indent=2)+'\n')
  print('progress',ai,'of',len(eligible),'candidates',result['tested'],'seconds',round(result['elapsed'],1),flush=True)
result['elapsed']=time.monotonic()-start
(ROOT/'mixed_fold_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
