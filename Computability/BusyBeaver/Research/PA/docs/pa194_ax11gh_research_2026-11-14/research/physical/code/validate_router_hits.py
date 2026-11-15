"""Reject provisional local hits; arithmetic-oracle passes are not box proofs."""
from common import c,load_case,startup_seed
from pathlib import Path
import sys,json
old,sites,_,cs=load_case('primary');expected=startup_seed(sites[25][0]);results=[]
for line in Path(sys.argv[1]).read_text().splitlines():
 parts=line.split(' | ');edits=[list(map(int,x.split())) for x in parts[:2]]
 rows={key:(w,d,88 if n==301 else n) for key,(w,d,n) in old.items() if key[0]!=301}
 for q,b,w,d,n in edits:rows[q,b]=(w,d==1,n)
 r=c.validate(rows,cs)
 tape=set();q=74;h=0;stop='bound'
 for step in range(200000):
  w,d,q=rows[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=1 if d else -1
  if q==254:stop='halt';break
  if q==35 and h>max(tape or {0}) and rows[35,0]==(1,True,35):stop='ray';break
  if q==84 and h==-2 and tape==expected:stop='seed';break
 results.append(dict(edits=edits,validation=r,startup_status=stop,startup_steps=step+1,
 startup_state=q,startup_head=h,arithmetic_row_changed=any(x[0] in c.BOXSTATES for x in edits),
 oracle_caveat='Changed arithmetic-box actions require new proofs; an oracle-only pass is insufficient.'))
assert len(results)==18
assert sum(x['validation']['ok'] for x in results)==11
assert not any(x['startup_status']=='seed' for x in results)
print(json.dumps(results,indent=2))
