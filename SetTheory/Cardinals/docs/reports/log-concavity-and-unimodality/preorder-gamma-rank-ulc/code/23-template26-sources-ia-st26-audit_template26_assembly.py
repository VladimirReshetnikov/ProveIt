#!/usr/bin/env python3
"""Fresh endpoint-support recount and polynomial decomposition, standard library only."""
import hashlib,itertools,json,time
from functools import lru_cache
from pathlib import Path
if not __debug__:raise SystemExit('Do not use -O/-OO')
D=Path(__file__).parent
SOURCE=Path('/workspace/shared/preorder-gamma-degree4/four-attachment/a4_polynomials.jsonl')
PIN='f5620b5901e86b497b5c5a24c398f8ccac318f130be23c4bfee5ec97103a9f26'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==PIN
row=next(r for line in SOURCE.open() if (r:=json.loads(line))['id']==26)
TYPES=(1,2,3,5,7,8,9,10,11,13,15)
assert row['core_rows']==[0,0,1,7] and row['orientation_mask']==8 and row['types']==list(TYPES)

def hall_count(adj,core):
 n=len(adj);incoming=0
 for x in adj:incoming|=x
 # 0 unused, 1 tail, 2 head; mandatory selected exteriors are never unused.
 opts=[([0] if v<core else [])+([1] if adj[v] else [])+([2] if incoming>>v&1 else []) for v in range(n)]
 out=[0]*5
 for status in itertools.product(*opts):
  tails=[v for v,s in enumerate(status) if s==1];heads=sum(1<<v for v,s in enumerate(status) if s==2)
  k=len(tails)
  if k!=heads.bit_count() or k>4:continue
  states={0}
  for v in tails:
   nxt=set()
   for used in states:
    choices=adj[v]&heads&~used
    while choices:
     bit=choices&-choices;choices-=bit;nxt.add(used|bit)
   states=nxt
  if heads in states:out[k]+=1
 return tuple(out)

@lru_cache(None)
def kernel(quota,kind):
 ext=[t for t,q in zip(TYPES,quota) for _ in range(q)]
 if kind=='Q':return hall_count([0,0,1]+[t&7 for t in ext],3)
 adj=[0,0,1,7]+[t&7 for t in ext]
 if kind=='full':
  for i,t in enumerate(ext):
   if t&8:adj[3]|=1<<(4+i)
 else:assert kind=='plus'
 return hall_count(adj,4)

start=time.perf_counter();scalar=0;nonzero=[0]*5
for pos,quota in enumerate(row['quota']):
 q=tuple(quota);full=kernel(q,'full');plus=kernel(q,'plus');R=[0]*5
 for j,t in enumerate(TYPES):
  if t&8 and q[j]:
   rem=list(q);rem[j]-=1
   qc=kernel(tuple(rem),'Q')
   for k in range(5):R[k]+=q[j]*qc[k]
 predicted=tuple(plus[k]+(R[k-1] if k else 0) for k in range(5))
 expected=tuple(row['gamma'][k][pos] for k in range(5))
 assert full==expected,(q,'source kernel',full,expected)
 assert predicted==full,(q,'decomposition',predicted,full)
 scalar+=5
 for k,c in enumerate(full):nonzero[k]+=bool(c)
receipt={'verdict':'PASS','date_utc':'2026-10-01','scope':'Fresh direct ordered disjoint support Hall counts for template26 and Gamma=Q_plus+tR, coefficientwise in integer-population binomial basis. No producer code imported.','quota_vectors':len(row['quota']),'all_scalar_coefficients':scalar,'nonzero_coefficients':nonzero,'sha256':{str(SOURCE):PIN,str(Path(__file__)):hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},'seconds':time.perf_counter()-start}
(D/'template26_assembly_algebra_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
