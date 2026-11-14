"""Delete a control by replacing every incoming edge with a whole local walk.
This permits several independently changed predecessor rows, with no kept-state
identification. All replacements are exact tape/position macro contractions.
"""
import symbolic_core as c
from pathlib import Path
from collections import defaultdict,Counter
import itertools,json,time
OUT=Path(__file__).resolve().parent
raw,labels=c.machine();inv={q:i for i,q in enumerate(labels)}
T={(inv[q],b):(w,1 if d else -1,inv[z])for(q,b),(w,d,z)in raw.items()}
P={inv[q]for q in c.BOXSTATES}|{75};R=12;ctx=defaultdict(set)
interesting={q for(q,b),(w,d,n)in T.items()if n not in P and n not in(q,196)}
def side(segs,n,count,left=False):
 out=[]
 for x in segs:
  if x[0]=='b':out.append(x[1])
  elif x[0]=='r':out.extend([x[1]]*min(count,x[2]*n+x[3]))
  else:
   out.append(0);out.append(0 if x[1]=='mark'and x[2]==0 else 1);out.extend([-1]*count)
  if len(out)>=count:return out[:count]
 return (out+([0]if left else[-1])*count)[:count]
def obs(s):
 q,onl,L,r=s;q=inv[q]
 if q not in interesting or onl:return
 for n in range(R+1):
  bs=side(L,n,R,True)[::-1]+side(r,n,R+1)
  b=bs[R]
  if b<0:continue
  if T[q,b][2]in P or T[q,b][2]in(q,196):continue
  w=sum((x==1)<<i for i,x in enumerate(bs));mask=sum((x>=0)<<i for i,x in enumerate(bs))
  ctx[q,b].add((w,mask))
start=time.monotonic();print(c.validate(raw,c.contracts(),obs),flush=True)
# Before the first clean frame.
tape=set();q=0;h=0
for _ in range(58154):
 b=int(h in tape);w,d,n=T[q,b]
 if n not in P and n not in(q,196):
  wi=sum((h+j in tape)<<(j+R)for j in range(-R,R+1));ctx[q,b].add((wi,(1<<(2*R+1))-1))
 if w:tape.add(h)
 else:tape.discard(h)
 h+=d;q=n
assert q==75
print('contexts',len(ctx),sum(map(len,ctx.values())),time.monotonic()-start,flush=True)

def outcomes(q,b,wi,mask,removed,limit=151):
 state=q;head=R;word=wi;ans={}
 for tick in range(limit):
  if not 0<=head<=2*R or not(mask>>head&1)or state==196:break
  rd=word>>head&1;w,d,state=T[state,rd]
  word=(word&~(1<<head))|w<<head;head+=d
  if state==removed:continue
  if head-R in(-1,1)and(word&~(1<<R))==(wi&~(1<<R)):
   act=(word>>R&1,head-R,state)
   ans.setdefault(act,tick+1)
 return ans

sol=[];counts=Counter()
for removed in sorted(set(range(196))-P):
 incoming=[(q,b)for(q,b),(w,d,n)in T.items()if n==removed and q!=removed]
 if not incoming or any(k not in ctx for k in incoming):continue
 counts['states']+=1;patch={};receipt={}
 for q,b in incoming:
  allowed=None;steps={}
  for wi,mask in ctx[q,b]:
   seen=outcomes(q,b,wi,mask,removed)
   allowed=set(seen)if allowed is None else allowed&set(seen)
   if not allowed:break
  if not allowed:break
  act=min(allowed,key=lambda x:(x[2]==q,x[1]!=T[q,b][1],x))
  patch[q,b]=act;receipt[f'{q},{b}']={'choices':sorted(allowed),'contexts':len(ctx[q,b])}
 else:
  # No predecessor points at the deleted control after the rewrites.
  tt={k:v for k,v in T.items()if k[0]!=removed};tt.update(patch)
  assert all(n!=removed for w,d,n in tt.values())
  item={'removed':removed,'patches':[(q,b,*act)for(q,b),act in patch.items()],'receipts':receipt}
  print('FOUND',item,flush=True);sol.append(item)
  (OUT/f'edge-contract-{len(sol)}.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(tt.items())))
print('RESULT',dict(counts),len(sol),'seconds',time.monotonic()-start,flush=True)
(OUT/'edge_contracts_result.json').write_text(json.dumps({'counts':dict(counts),'solutions':sol,'seconds':time.monotonic()-start},indent=2)+'\n')
