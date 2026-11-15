"""Sound zero/positive dataflow, testing simple direct register aliases."""
from common import load_case
from collections import deque
import json
_,_,ins,_=load_case('primary')
reached=[set() for _ in ins];todo=deque([(25,1)]);reached[25].add(1)
while todo:
 i,m=todo.popleft();op=ins[i]
 if op[0]=='inc':nxt=[(op[2],m|1<<op[1])]
 elif op[0]=='dec':
  r=op[1];nxt=[(op[3],m),(op[3],m&~(1<<r))] if m>>r&1 else [(op[2],m)]
 elif op[0]=='jump':nxt=[(op[1],m)]
 else:nxt=[]
 for j,n in nxt:
  if n not in reached[j]:reached[j].add(n);todo.append((j,n))
pairs=[]
for a in range(9):
 for b in range(a+1,9):
  conflicts=[]
  for i,op in enumerate(ins):
   if op[0] in ('inc','dec') and op[1] in (a,b):
    other=a^b^op[1]
    if any(m>>other&1 for m in reached[i]):conflicts.append(i)
  pairs.append(dict(pair=[a,b],conflict_sites=len(conflicts),first_conflicts=conflicts[:8]))
assert sum(map(len,reached))==263888
assert sum(bool(x) for x in reached)==3671
assert len(pairs)==36 and all(x['conflict_sites'] for x in pairs)
print(json.dumps(dict(reachable_abstract_states=263888,reachable_sites=3671,pairs=pairs,
 scope='No direct pair alias certified under this abstraction; not an impossibility proof for stronger invariants or encodings.'),indent=2))
