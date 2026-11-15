from common import *
from collections import defaultdict
import time,itertools
begin=time.monotonic();seen=defaultdict(dict)
for i,c in enumerate(contracts):
 k=[0]
 def obs(x):
  if i not in seen[x[0]]:seen[x[0]][i]=(k[0],x)
  k[0]+=1
 s.run(rows,c,observe=obs)
print('contexts',len(contracts),len(seen),time.monotonic()-begin,flush=True)
controls=sorted({q for q,b in rows});others=sorted(set(controls)-s.BOXSTATES-{84,74})
base_protected=[3,16,113]
trials=0;hits=[]
for b in base_protected:
 for ia,a in enumerate(others):
  cis=set(seen[a])|set(seen[b]);short=[]
  for i in sorted(cis):
   c=contracts[i];poss=[]
   if i in seen[a]:poss.append(seen[a][i])
   if i in seen[b]:poss.append(seen[b][i])
   _,st=min(poss,key=lambda x:x[0]);st=(b if st[0]==a else st[0],)+st[1:]
   short.append((c[0],c[1],st,c[3]))
  tr={(q,r):(w,d,b if t==a else t) for(q,r),(w,d,t) in rows.items() if q!=a}
  for w,d,t in itertools.product((0,1),(False,True),controls+[254]):
   if t==a:continue
   tr[b,0]=w,d,t;trials+=1
   for c in short:
    if s.run(tr,c) is None:break
   else:
    valid=s.validate(tr,contracts)
    hit={'removed':a,'merged':b,'row0':[w,d,t],'result':valid}
    hits.append(hit);print('HIT',hit,flush=True)
    (HERE/f'candidate_{b}_{a}_{w}_{int(d)}_{t}.tm').write_text(''.join(f'{q} {r} {u} {"R" if v else "L"} {z}\n' for(q,r),(u,v,z) in sorted(tr.items())))
  if ia%20==0:print('progress',b,a,trials,time.monotonic()-begin,flush=True)
(HERE/'fresh_box_edge_results.json').write_text(json.dumps({'trials':trials,'source_contracts':len(contracts),'hits':hits,'elapsed':time.monotonic()-begin},indent=2)+'\n')
print('DONE',trials,hits,flush=True)
