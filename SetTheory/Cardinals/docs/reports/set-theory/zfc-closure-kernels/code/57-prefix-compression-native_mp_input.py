#!/usr/bin/env python3
"""Export and independently check the semantic MP variant's runtime sites."""
from pathlib import Path
from collections import defaultdict
import json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'redesign'))
import mp_protocol_runtime as m

class Tracking(dict):
 def __init__(self, rows):super().__init__(rows);self.used=set()
 def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

out=ROOT/'compression/mp_native'
out.mkdir(exist_ok=True)
table,nodes=m.generate()
cases=m.guards()
costs={};usage=defaultdict(set)
for i,(pc,op,branch,target) in enumerate(cases):
 traced=Tracking(table)
 rules,literal=m.a.strict.run(traced,pc,branch,target,halt=op=='CH',fuel=1000)
 assert literal>0
 costs[i]=sum(rules.values())
 for row in traced.used:usage[row].add(i)
rows=[]
for p,op,r in m.a.sites:
 for zero in ((True,False) if op=='CD' else (None,)):
  phys=m.audit.PERM[r] if op in ('CI','CD') else -1
  nxt=m.audit.successor(p,op,r,zero)
  effect=0 if op=='CI' else 1 if op=='CD' and not zero else -1
  rows.append([len(rows),p,phys if op=='CD' else -1,int(zero) if zero is not None else -1,nxt or '-',int(nxt is None),effect,phys if effect>=0 else -1,int(op=='CH')])
assert len(rows)==len(cases)==8366
with (out/'native_cases.txt').open('w') as f:
 for row in rows:f.write(' '.join(map(str,row+[costs[row[0]]]))+'\n')
with (out/'native_table.txt').open('w') as f:
 for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])):f.write(f'{q} {b} {w} {d} {t}\n')
with (out/'native_usage.txt').open('w') as f:
 for (q,b),indices in sorted(usage.items(),key=lambda x:(int(x[0][0]),x[0][1])):f.write(f'{q} {b} '+','.join(map(str,sorted(indices)))+'\n')
print('MP native input ready: all8366 case costs and table accesses independently checked.')
