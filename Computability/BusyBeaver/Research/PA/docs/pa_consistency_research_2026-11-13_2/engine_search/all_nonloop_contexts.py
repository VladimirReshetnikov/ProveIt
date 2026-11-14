import symbolic_core as c
from collections import defaultdict,Counter
from pathlib import Path
import json,time
OUT=Path(__file__).resolve().parent
raw,labels=c.machine();inv={q:i for i,q in enumerate(labels)}
T={(inv[q],b):(w,1 if d else -1,inv[z])for(q,b),(w,d,z)in raw.items()}
PURE={q for q in range(196) if labels[q] not in c.BOXSTATES and all(T[q,b][2]!=q for b in(0,1))}
R=12;out=defaultdict(set)
def side(segs,n,count,left=False):
 r=[]
 for x in segs:
  if x[0]=='b':r.append(x[1])
  elif x[0]=='r':r.extend([x[1]]*min(count,x[2]*n+x[3]))
  else:
   r.append(0)
   if x[1]=='mark' and x[2]==0:r.append(0)
   elif x[1]in('none','inc','dec','mark'):r.append(1)
   r.extend([-1]*count)
  if len(r)>=count:return r[:count]
 return (r+([0]if left else[-1])*count)[:count]
def obs(s):
 q,onl,L,r=s;q=inv[q]
 if q not in PURE or onl:return
 for n in range(R+1):
  w=side(L,n,R,True)[::-1]+side(r,n,R+1)
  v=sum((b==1)<<i for i,b in enumerate(w));m=sum((b!=-1)<<i for i,b in enumerate(w))
  if not(m>>R&1):
   for b in(0,1):out[q].add((v|b<<R,m|1<<R))
  else:out[q].add((v,m))
start=time.monotonic();print(c.validate(raw,c.contracts(),obs),flush=True)
# Prefix startup finite trace is included until clean root, but no new reader typically occurs.
tape=set();q=0;h=0
for i in range(58154):
 if q in PURE:
  v=sum((h+j in tape)<<(j+R)for j in range(-R,R+1));out[q].add((v,(1<<(2*R+1))-1))
 b=int(h in tape);w,d,q=T[q,b]
 if w:tape.add(h)
 else:tape.discard(h)
 h+=d
assert q==75
print('contexts',len(out),sum(map(len,out.values())),'seconds',time.monotonic()-start,flush=True)
(OUT/'all_nonloop_contexts.json').write_text(json.dumps({'radius':R,'contexts':{str(q):sorted(v)for q,v in out.items()}},separators=(',',':'))+'\n')
