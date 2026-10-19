from pathlib import Path
from itertools import product
import json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError("Assertions required")
ROOT=Path(__file__).resolve().parent.parent
oldp=ROOT/'baseline243/sources/candidate-combined243__zfc_combined243_old.tm'
newp=ROOT/'runtime/survivor_1_old.tm'
def read(p):
 d={}
 for s in p.read_text().splitlines():
  if s and not s.startswith('#'):
   q,b,w,m,r=s.split();d[int(q),int(b)]=(int(w),1 if m=='R' else -1,int(r))
 return d
O,N=read(oldp),read(newp)
def inv(q,h,S):
 return (q not in (15,18,47,65) or h-1 not in S) and (q!=27 or h not in S)
def step(T,q,h,S):
 assert -2<=h<=2, (q,h)
 w,m,r=T[q,int(h in S)];S=set(S)
 if w:S.add(h)
 else:S.discard(h)
 return r,h+m,S
states=sorted({q for q,b in O});checks=0;blocks=0
for q in states:
 for bits in product((0,1),repeat=5):
  S={i-2 for i,b in enumerate(bits) if b}
  if not inv(q,0,S):continue
  r,h,U=step(O,q,0,S)
  assert inv(r,h,U),(q,bits,r,h,U)
  checks+=1
  v,k,V=(15 if q==27 else q),0,set(S)
  n=3 if q==15 and 0 not in S else 1
  for _ in range(n):
   assert v!=254
   v,k,V=step(N,v,k,V)
  assert (v,k,V)==(15 if r==27 else r,h,U),(q,bits,n,(r,h,U),(v,k,V))
  blocks+=1
assert inv(95,0,set())
# Every examined transition reads/writes only within[-2,2]; outside tape arbitrary.
res={'status':'PASS_INDUCTIVE_ALL_TAPE_POSITIVE_BLOCK_SIMULATION','old_states':len(states),'new_states':len({q for q,b in N}),'finite_local_implications':checks,'positive_block_checks':blocks,'state_map':'27->15, identity elsewhere','block_lengths':[1,3],'initial_state':95,'initial_head_and_tape':'arbitrary','invariant':'q in {15,18,47,65} implies left bit0; q27 implies current bit0','result':'halting equivalent; finite halting times t_old <= t_new <=3*t_old','scope':'ordinary finite-local proof certificate, not a Lean proof'}
p=Path(__file__).parent/'fold15_local_proof_result.json';p.write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
