#!/usr/bin/env python3
import json,time,itertools,collections
from pathlib import Path
import symbolic_runtime as s
P=Path(__file__).resolve().parent
rows={}
for ln in (P/'pa194.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
sites=json.loads((P/'sites.json').read_text()); ins=json.loads((P/'instructions.json').read_text())
cs=[]
for i,code in enumerate(ins):
 st=s.frame(tuple(map(int,sites[i][0])))
 f=lambda j,extra=0,effect=s.PLAIN:s.canonical(s.frame(tuple(map(int,sites[j][0])),extra,effect))
 if code[0]=='inc':
  _,r,n=code;cs.append((i,None,st,f(n,0,('x','inc',s.PHYSICAL[r]))))
 elif code[0]=='dec':
  _,r,z,p=code;cs.append((i,(s.PHYSICAL[r],True),st,f(z)));cs.append((i,(s.PHYSICAL[r],False),st,f(p,1,('x','dec',s.PHYSICAL[r]))))
 elif code[0]=='jump':cs.append((i,None,st,f(code[1])))
 else:cs.append((i,None,st,None))
byq=collections.defaultdict(set); snapshots={}
for k,c in enumerate(cs):
 def observe(st):
  byq[st[0]].add(k)
  if (k,st[0]) not in snapshots: snapshots[k,st[0]]=st
 if s.run(rows,c,observe=observe) is None:raise ValueError(c[:2])
print('collected',len(cs),'contracts',sum(map(len,byq.values())),'incidences',flush=True)
start=time.time();count=0;success=[];states=sorted(set(q for q,b in rows)-s.BOXSTATES-{84})
failure=collections.Counter()
for ai,a in enumerate(states):
 for b in states[ai+1:]:
  affected=sorted(byq[a]|byq[b],key=lambda k:-failure[k])
  if not affected:continue
  # Early test from the first baseline occurrence of either changed control.
  local=[]
  for k in affected:
   c=cs[k]; sa=snapshots.get((k,a)); sb=snapshots.get((k,b))
   # Each state occurrence is a necessary independent continuation check.
   for st in (sa,sb):
    if st is not None:local.append((k,(c[0],c[1],st,c[3])))
  oldacts=[rows[a,0],rows[a,1],rows[b,0],rows[b,1]]
  for r0,r1 in itertools.product(set([oldacts[0],oldacts[2]]),set([oldacts[1],oldacts[3]])):
   count+=1
   rr={(q,v):(w,d,b if n==a else n) for (q,v),(w,d,n) in rows.items() if q!=a}
   rr[b,0]=(r0[0],r0[1],b if r0[2]==a else r0[2]);rr[b,1]=(r1[0],r1[1],b if r1[2]==a else r1[2])
   for k,c in local:
    st=c[2];cc=(c[0],c[1],(b if st[0]==a else st[0],)+st[1:],c[3])
    if s.run(rr,cc,fuel=2048) is None:failure[k]+=1;break
   else:
    v=s.validate(rr,cs)
    if v['ok']:
     hit={'remove':a,'keep':b,'r0':rr[b,0],'r1':rr[b,1],'verification':v}
     success.append(hit);print('HIT',hit,flush=True)
 if ai%10==0:print('progress',ai,len(states),count,round(time.time()-start,2),'hits',len(success),flush=True)
receipt={'candidates':count,'seconds':time.time()-start,'hits':success,'scope':'Merge pair with each replacement row chosen from either original row; preserve complete source-instruction symbolic endpoint; excludes arithmetic boxes and boundary84.'}
(P/'whole_instruction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
