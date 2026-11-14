"""A sufficient zero/nonzero register coalescing test; no precision claim."""
from pathlib import Path
from collections import Counter,deque
import json
import symbolic_runtime as c

_,instructions,_=c.source()
seen=set();pending=deque([(25,1)])
observed=[set() for _ in range(9)]
sites=Counter()
while pending:
 q,mask=pending.popleft()
 if (q,mask) in seen:continue
 seen.add((q,mask));sites[q]+=1
 instruction=instructions[q];op=instruction[0]
 if op=='inc':
  r,n=instruction[1:];observed[r].add(mask);pending.append((n,mask|(1<<r)))
 elif op=='dec':
  r,z,p=instruction[1:];observed[r].add(mask)
  if mask&(1<<r):
   pending.append((p,mask));pending.append((p,mask&~(1<<r)))
  else:pending.append((z,mask))
 elif op=='jump':pending.append((instruction[1],mask))
 elif op!='halt':raise ValueError(instruction)

conflicts={}
for a in range(9):
 for b in range(a+1,9):
  conflicts[f'{a},{b}']=sum(bool(m>>b&1)for m in observed[a])+sum(bool(m>>a&1)for m in observed[b])
receipt={'initial_source_site':25,'initial_positive_mask':1,
 'abstract_configurations':len(seen),'reachable_source_sites':len(sites),
 'maximum_masks_per_site':max(sites.values()),
 'conflict_mask_counts':conflicts,
 'pairs_certified_coalescible':[k for k,v in conflicts.items()if v==0],
 'scope':'Sufficient zero/nonzero abstraction only; empty result is not impossibility.'}
Path(__file__).with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='conflict_mask_counts'},indent=2))
