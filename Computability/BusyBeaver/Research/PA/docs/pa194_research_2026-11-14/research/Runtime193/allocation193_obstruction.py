#!/usr/bin/env python3
"""Nine exact traces rule out all 9! register allocations for this fixed core.
This is an obstruction for a specified core/selector rewrite family only.
"""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent
PK=ROOT/'inputs'
def read(path):
 r={}
 for line in path.read_text().splitlines():
  q,b,w,d,t=line.split();r[int(q),int(b)]=int(w),1 if d=='R'else -1,int(t)
 return r
old=read(PK/'primary194.native.tm');core=read(PK/'runtime193.native.tm')
SK=[51,36,25,48,32,33,22,55,60]
BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
# Only genuine source-to-register selectors are permuted. In particular the
# new fold helper 88/0 ->51 is not a register selector and is not permuted.
selectors={key:SK.index(n)for key,(w,d,n)in old.items()if key[0]not in BOX and n in SK}
records=[]
for k in range(9):
 rows=dict(core)
 perm=list(range(9));perm[7],perm[k]=perm[k],perm[7]
 for key,i in selectors.items():
  if key in rows:
   w,d,n=rows[key];rows[key]=w,d,SK[perm[i]]
 q,h,ones=74,0,set();trace=[];selector_hits=set()
 for step in range(1000):
  b=int(h in ones)
  if q==35 and not b and (not ones or h>max(ones)):
   assert rows[35,0]==(1,1,35)
   break
  assert q!=254
  if(q,b)in selectors:selector_hits.add((q,b))
  w,d,n=rows[q,b];trace.append([q,h,b,w,d,n]);(ones.add if w else ones.discard)(h);q,h=n,h+d
 else:raise AssertionError('no certified ray')
 assert selector_hits=={(45,1)}
 assert selectors[45,1]==7
 records.append(dict(physical_H=k,transitions=len(trace),state=q,head=h,ones=sorted(ones),selector_rows=[list(x)for x in sorted(selector_hits)],trace=trace))
result={'status':'PASS','family_size':362880,'representative_cases':9,'common_start':74,'all_conclude':'outward right ray in state35 with 35/0 = 1R35','only_permutation_sensitive_row_visited':[45,1],'core_sha256':hashlib.sha256((PK/'runtime193.native.tm').read_bytes()).hexdigest(),'cases':records,'scope':'All physical-register permutations of the exact runtime193 core, changing only genuine external selector targets; no other edits and fixed blank start74.'}
(ROOT/'evidence/allocation193_obstruction.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items()if k!='cases'},indent=2));print('trace lengths',[r['transitions']for r in records])
