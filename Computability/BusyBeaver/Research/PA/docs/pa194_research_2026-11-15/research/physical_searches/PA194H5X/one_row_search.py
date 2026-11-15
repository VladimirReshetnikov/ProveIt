#!/usr/bin/env python3
from search_support import *
start=time.time();count=0;success=[];states=sorted(set(q for q,b in rows)-s.BOXSTATES-{84});failure=collections.Counter()
pairs=[]
for ai,a in enumerate(states):
 for b in states[ai+1:]:
  for free in (0,1):
   if rows[a,1-free]==rows[b,1-free]:pairs.append((a,b,free))
print('pairs',len(pairs),flush=True)
for pi,(a,b,free) in enumerate(pairs):
 affected=sorted(byq[a]|byq[b],key=lambda k:-failure[k]);local=[]
 for k in affected:
  c=cs[k]
  for q in (a,b):
   st=snapshots.get((k,q))
   if st is not None:local.append((k,(c[0],c[1],(b if st[0]==a else st[0],)+st[1:],c[3])))
 rr={(q,v):(w,d,b if n==a else n) for (q,v),(w,d,n) in rows.items() if q!=a}
 for w,d,n in itertools.product((0,1),(False,True),set(q for q,v in rr)):
  count+=1;rr[b,free]=w,d,n
  for k,c in local:
   if s.run(rr,c,fuel=2048) is None:failure[k]+=1;break
  else:
   v=s.validate(rr,cs)
   if v['ok']:
    hit={'remove':a,'keep':b,'free_bit':free,'action':rr[b,free],'verification':v};success.append(hit);print('HIT',hit,flush=True)
 if pi%10==0:print('progress',pi,len(pairs),count,round(time.time()-start,2),'hits',len(success),flush=True)
receipt={'candidates':count,'pairs':len(pairs),'seconds':time.time()-start,'hits':success,'scope':'Merge pair with one shared row; synthesize other row over every write, move and remaining working target; preserve complete source-instruction endpoint, boxes and boundary84 excluded.'}
(P/'one_row_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
