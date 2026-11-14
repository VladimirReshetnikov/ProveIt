"""Screen state identifications by entire symbolic instruction endpoint.
Unlike step/window tests, intermediate configurations need not align.
"""
import symbolic_core as c
from collections import defaultdict,Counter
from pathlib import Path
import json,time,itertools
OUT=Path(__file__).resolve().parent
rows,labels=c.machine();cs=c.contracts()
# Store a boundary at first physical occurrence in every source contract.
visits=defaultdict(dict);start=time.monotonic()
for ci,cc in enumerate(cs):
 def obs(s):
  if not s[1] and s[0] not in c.BOXSTATES and s[0]!=84:visits[s[0]].setdefault(ci,s)
 assert c.run(rows,cc,observe=obs)is not None
print('indexed',len(visits),sum(map(len,visits.values())),time.monotonic()-start,flush=True)
# Prefer shortest proof suffixes, with varying branches interleaved later.
order={q:sorted(states,key=lambda ci:len(states[ci][2])+len(states[ci][3]))for q,states in visits.items()}

def runremaining(T,cc,s,fuel=1024):
 ci,br,_,target=cc
 for k in range(fuel):
  if s[0]==254 if target is None else c.matches(s,target):return k
  nxt=c.sstep(T,br,s)
  if nxt is None:return None
  s,_=nxt
 return None

counts=Counter();sol=[];keys=sorted({q for q,b in rows})
for ix,drop in enumerate(sorted(visits)):
 for keep in keys:
  if keep==drop:continue
  counts['pairs']+=1
  T={(q,b):(w,d,keep if z==drop else z)for(q,b),(w,d,z)in rows.items()if q!=drop}
  passed=True
  for ci in order[drop]:
   s=visits[drop][ci];s=(keep,*s[1:])
   counts['contracts_tested']+=1
   if runremaining(T,cs[ci],s) is None:
    passed=False;break
  if passed:
   item={'drop':drop,'keep':keep,'affected_contracts':len(order[drop])}
   print('SURVIVOR',item,flush=True);sol.append(item)
   (OUT/f'macro-quotient-{len(sol)}.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(T.items())))
 if ix%20==19:print('progress',ix+1,dict(counts),'seconds',time.monotonic()-start,flush=True)
print('RESULT',dict(counts),sol,'seconds',time.monotonic()-start,flush=True)
(OUT/'macro_quotients_result.json').write_text(json.dumps({'counts':dict(counts),'solutions':sol,'seconds':time.monotonic()-start},indent=2)+'\n')
