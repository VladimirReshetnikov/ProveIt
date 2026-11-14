#!/usr/bin/env python3
"""Necessary finite-case filter for changing 74/0 in the 193-state runtime.

Run the actual increment macro, including the marked unary register file.
Accept arbitrary valid nonempty spare tails, not just the stock appended [1].
A passing candidate still needs a proof for arbitrary register values/tails.
"""
from pathlib import Path
import itertools,json,random,time
P=Path(__file__).resolve().parent
source=P/'runtime193.native.tm'
rows={(int(q),int(b)):(int(w),1 if d=='R'else-1,int(n))for q,b,w,d,n in map(str.split,source.read_text().splitlines())}
cases=[]
for vs in [[0]*10,[1]*10,[0]*9+[3,0,1],[2,0,1,3,2,1,0,2,3,2]]:
 for r in [8,0,1,2,3,4,5,6,7]:cases.append((vs,r))
rng=random.Random(74193)
for i in range(40):cases.append(([rng.randrange(5)for _ in range(rng.randrange(10,14))],rng.randrange(9)))

def run(act,vs,r,bound=3000):
 one={-1,-3,-4};left={-1,-3,-4};pos=0;starts=[]
 for i,v in enumerate(vs):
  starts.append(pos);one.update(range(pos+1,pos+v+2));pos+=v+2
 one.remove(starts[r]+1);q,h=64,0;seen=set()
 for k in range(bound):
  if k and q==40 and h==-1:
   out=[];p=0;hi=max(one)
   if {x for x in one if x<0}!=left:return None
   while p<hi:
    if p in one or p+1 not in one:return None
    z=p+1
    while z in one:z+=1
    out.append(z-p-2);p=z
   want=vs[:9];want[r]+=1
   if len(out)<10 or out[:9]!=want:return None
   return {'steps':k,'tail':out[9:]}
  if h < -8 or h>pos+50 or(q,0)not in rows:return None
  key=(q,h,tuple(sorted(one)))
  if key in seen:return None
  seen.add(key);b=int(h in one)
  w,d,n=act if(q,b)==(74,0)else rows[q,b]
  (one.add if w else one.discard)(h);q,h=n,h+d
 return None

good=[];bins={};start=time.time()
for q in sorted({q for q,b in rows}):
 for w,d in itertools.product([0,1],[-1,1]):
  act=(w,d,q);res=[]
  for vs,r in cases:
   z=run(act,vs,r)
   if z is None:break
   res.append(z)
  bins[len(res)]=bins.get(len(res),0)+1
  if len(res)==len(cases):
   good.append({'action':act,'results':res});print({'action':act,'passed':len(res)},flush=True)
ans={'search':'74/0 actual marked increment, arbitrary valid spare-tail acceptance','step_bound':3000,'cases':cases,'pass_count_histogram':bins,'results':good,'seconds':time.time()-start}
(P/'inc74_spare_left_detours.json').write_text(json.dumps(ans,indent=2)+'\n')
print({'candidate_count':len(good),'histogram':bins,'seconds':ans['seconds']})
