"""Literal test of the documented ZFC marker-relay recipe on AX11GH."""
from common import c,load_case
import json
old,_,_,cs=load_case('gh')
rows={key:(w,d,88 if n==301 else n) for key,(w,d,n) in old.items() if key[0]!=301}
rows.update({(88,0):(0,False,51),(51,0):(0,True,122),(36,0):(1,True,16),(16,1):(1,False,56)})
for q in [42,47,57,126,139,141]:rows[q,1]=(0,False,122)
res=c.validate(rows,cs);assert not res['ok']
tape=set();h=0;q=74;trace=[];status='bound'
for step in range(1000000):
 trace.append([step,q,h,sorted(tape)])
 w,d,q=rows[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=1 if d else -1
 if q==254:status='halt';break
 if q==35 and h>max(tape or {0}) and rows[35,0]==(1,True,35):status='certified_outward_ray';break
assert status=='certified_outward_ray'
print(json.dumps(dict(validation=res,steps=step+1,state=q,head=h,ones=sorted(tape),
 startup_status=status,trace=trace,scope='Rejected direct transplantation. No claim against other relay/source redesigns.'),indent=2))
