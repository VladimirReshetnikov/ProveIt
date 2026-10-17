#!/usr/bin/env python3
"""Literal positive-decrement continuation samples for route-entry synthesis."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'redesign'))
import prefix_decrement as p
table=p.generate();out=ROOT/'compression/prefix_route_native';out.mkdir(exist_ok=True)
rows=[]
for index,case in enumerate(p.cases()):
 pc,r,regs,gap,spares=case
 q,h,ones=96,0,p.m.audit.paint(pc,gap,regs,spares,0)
 for step in range(5000):
  if q==75 and h in ones:break
  w,d,q=table[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R' else -1
 else:raise AssertionError(('cannot reach positive route',index,case))
 nxt=p.m.audit.successor(pc,'CD',r,False)
 outhead=-(nxt is None);outgap=gap+1+(nxt is None)
 newregs=regs.copy();newregs[r]-=1
 target=p.m.audit.paint('' if nxt is None else nxt,outgap,newregs,spares,outhead)
 rows.append((index,r,h,outhead,tuple(sorted(ones)),tuple(sorted(target))))
# Spread the shortest representative continuations across physical registers.
preferred=[]
for r in range(9):
 rcases=[row for row in rows if row[1]==r]
 preferred.extend(rcases[:9])
preferred_ids={row[0] for row in preferred}
rows=preferred+[row for row in rows if row[0] not in preferred_ids]
with (out/'cases.txt').open('w') as f:
 for i,r,h,oh,ones,target in rows:
  f.write(' '.join(map(str,[i,r,h,oh,len(ones),len(target),*ones,*target]))+'\n')
(out/'table.tm').write_bytes(p.m.audit.encode(table))
(out/'metadata.json').write_text(json.dumps(dict(cases=len(rows),search_order='First nine cases of each physical register, then remaining source-site samples',scope='Concrete positive-decrement samples starting at old75/read1; no universal theorem'),indent=2)+'\n')
print('Exported',len(rows),'positive continuation samples.')
