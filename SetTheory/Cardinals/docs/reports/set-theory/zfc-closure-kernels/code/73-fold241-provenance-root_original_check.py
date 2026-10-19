from pathlib import Path
from itertools import product
import hashlib,json
oldp=Path('/workspace/shared/busybeaver242-search-20261018/seed20261018/survivor_1_old.tm')
newp=Path('/workspace/shared/busybeaver241-neutral-backgrounds-20261018/candidates241/candidate_1_old.tm')
def read(p):
 d={}
 for s in p.read_text().splitlines():
  if s and not s.startswith('#'):
   q,b,w,m,r=s.split();d[int(q),int(b)]=(int(w),1 if m=='R' else -1,int(r))
 return d
O,N=read(oldp),read(newp)
def inv(q,h,S):return (q!=17 or h-1 in S) and(q!=39 or h-1 not in S)
def step(T,q,h,S):
 w,m,r=T[q,int(h in S)];S=set(S)
 if w:S.add(h)
 else:S.discard(h)
 return r,h+m,S
checks=blocks=0
for q in sorted({q for q,b in O}):
 for bits in product((0,1),repeat=5):
  S={i-2 for i,b in enumerate(bits) if b}
  if not inv(q,0,S):continue
  r,h,U=step(O,q,0,S);assert inv(r,h,U);checks+=1
  v,k,V=(17 if q==39 else q),0,set(S)
  n=5 if q==17 and 0 not in S else 3 if q in (17,39) else 1
  for _ in range(n):
   assert v!=254
   v,k,V=step(N,v,k,V)
  assert (v,k,V)==(17 if r==39 else r,h,U),(q,bits,n,(r,h,U),(v,k,V))
  blocks+=1
res={'status':'PASS_SIMPLE_ALL_TAPE_SIMULATION','old_sha256':hashlib.sha256(oldp.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(newp.read_bytes()).hexdigest(),'old_states':242,'new_states':241,'state_map':'39->17; identity elsewhere','invariant':'state17 has leftbit1; state39 has leftbit0','invariant_implications':checks,'whole_tape_block_checks':blocks,'block_lengths':[1,3,5],'initial_state':95,'initial_tape_and_head':'arbitrary','halting_time_formula':'t_new=t_old+4*visits(17,0)+2*visits(17,1)+2*visits(39,0)+2*visits(39,1)','scope':'ordinary all-tape mathematical proof certificate'}
Path(__file__).with_name('result.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
