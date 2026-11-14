"""Recover which non-engine edges select each unary register."""
import symbolic_core as c
from collections import defaultdict,Counter
from pathlib import Path
import json
T,labels=c.machine();sites,ins=c.program();cs=c.contracts()
SK=set(c.SK);entry_calls=defaultdict(set);dummy=defaultdict(set);seen=set()
for case in cs:
 i,br,s,target=case;pending=None;count=0
 for k in range(1024):
  if count and(s[0]==254 if target is None else c.matches(s,target)):break
  q,onl,L,R=s
  if not onl and R and R[0][0]=='x' and R[0][1]=='none' and q in SK:
   assert pending is not None,(case,s)
   entry_calls[pending].add((sites[i][1],sites[i][2],c.SK.index(q)))
   pending=None
  nq=c.sstep(T,br,s)
  if nq is None:raise RuntimeError((i,k,s))
  next,moved=nq
  if moved and next[0] in SK and q not in SK:
   assert not onl and R[0][0]=='b'
   if pending:dummy[pending].add((i,q))
   pending=(q,R[0][1]);seen.add(pending)
  elif moved and q in SK and next[0] not in SK:
   if pending:dummy[pending].add((i,q));pending=None
  s=next;count+=moved
 else:raise RuntimeError(i)
 if pending:dummy[pending].add((i,-1))
print('entries',len(seen))
report=[]
for edge in sorted(seen):
 w,d,z=T[edge];p=c.SK.index(z)
 calls=entry_calls[edge]
 item={'edge':edge,'old_target':z,'skip_index':p,'calls':sorted(calls),'dummies':len(dummy[edge]),'dummy_samples':sorted(dummy[edge])[:5]}
 print(item);report.append(item)
(Path(__file__).resolve().parent/'register_entry_analysis.json').write_text(json.dumps(report,indent=2)+'\n')
