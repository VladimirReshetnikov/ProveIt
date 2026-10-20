#!/usr/bin/env python3
"""Exact218-state initialized core and an explicit proof of its blank failure.

No claim of a218-state blank-tape Con(ZFC) construction is made. Every assertion
below concerns literal finite computation, source prefixes, or a one-row loop.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,hashlib,sys
BASE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
CORE_SHA='cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f'
SOURCE_SHA='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,o):Path(p).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def parse(p):
 t={};starts=[]
 for line in Path(p).read_text().splitlines():
  if line.startswith('#! start '):starts.append(int(line.split()[-1]))
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in t
   t[q,b]=(w,1 if d=='R'else-1,z)
 assert starts==[0];return t

def raw(t):return('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def prefix(t,p):
 c={-1:1,**{i:int(b)for i,b in enumerate(p)}};before=dict(c);q=84;h=0
 for n in range(10000):
  if h==len(p):assert c==before;return q,n
  assert h in c;w,d,q=t[q,c[h]];c[h]=w;h+=d
 raise AssertionError('Prefix bound')
def finite(t,q,h,c,n):
 c=dict(c);trace=[]
 for i in range(n):
  assert h in c;w,d,z=t[q,c[h]];trace.append([q,h,c[h],w,d,z]);c[h]=w;q=z;h+=d
 return q,h,c,trace

def blank(t,n):
 q=h=0;ones=set();trace=[]
 for k in range(n):
  b=int(h in ones);w,d,z=t[q,b];trace.append([k,q,h,b,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d
 return q,h,ones,trace

def main():
 a=argparse.ArgumentParser(description=__doc__)
 for s in('baseline','core','sites','output'):a.add_argument('--'+s,type=Path,required=True)
 x=a.parse_args();assert __debug__ and not sys.flags.optimize
 oldfile=x.baseline/'machine/k219.native.tm';oldsrc=x.baseline/'machine/sites219.json'
 assert sha(oldfile)==BASE_SHA and sha(oldsrc)==SOURCE_SHA and sha(x.sites)==SOURCE_SHA
 old=parse(oldfile);new={(q,b):(w,d,88 if z==301 else z)for(q,b),(w,d,z)in old.items()if q!=301}
 new[88,0]=(0,-1,51);new[51,0]=(0,1,122)
 assert raw(new)==x.core.read_bytes() and sha(x.core)==CORE_SHA
 Q={q for q,b in new};assert len(Q)==218 and set(new)=={(q,b)for q in Q for b in(0,1)}
 assert{z for w,d,z in new.values()}-Q=={254}
 rows=json.loads(x.sites.read_text());ps={p[:i]for p,op,arg in rows for i in range(len(p))}
 paths=defaultdict(list);timing=Counter();oq=set();nq=set()
 for p in sorted(ps,key=lambda p:(len(p),p)):
  u,nu=prefix(old,p);v,nv=prefix(new,p);assert v==(88 if u==301 else u)
  paths[u].append(p);timing[nv-nu]+=1;oq.add(u);nq.add(v)
 assert(len(rows),len(ps),len(oq),len(nq))==(4744,4743,169,168)
 assert len(paths[301])==len(paths[88])==4
 assert all(p.endswith('0')for p in paths[301])and all(p.endswith('1')for p in paths[88])
 lemmas=[]
 for pred,q,steps,target in[(0,301,5,45),(1,88,3,122)]:
  cells={-1:pred,0:0};a1=finite(old,q,0,cells,1);a2=finite(new,88,0,cells,steps)
  assert a1[:3]==a2[:3]==(target,1,cells)
  lemmas.append(dict(previous_bit=pred,old_state=q,old_steps=1,new_steps=steps,target=target,old_trace=a1[3],new_trace=a2[3],exterior='arbitrary and untouched'))
 a1=finite(old,51,0,{0:0,1:1},2);a2=finite(new,51,0,{0:0,1:1},2)
 assert a1[:3]==a2[:3]==(1,0,{0:0,1:0})
 lemmas.append(dict(role='old51 with right neighbor1',old_trace=a1[3],new_trace=a2[3],exterior='arbitrary and untouched'))
 assert new[88,1]==old[88,1]==old[301,1]and new[51,1]==old[51,1]
 o79=blank(old,79);n79=blank(new,79)
 assert o79[:3]==n79[:3]==(51,5,{-3,-2})
 q,h,ones,tr=blank(new,85);assert(q,h,ones)==(35,7,{-3,-2})and new[35,0]==(1,1,35)
 # Every subsequent scanned cell is a previously untouched zero to the right.
 # Induction onk gives state35, head7+k, support{-3,-2} union[7,7+k).
 failure=dict(status='BLANK_NONHALTING_RAY_PROVED',first_divergent_step=79,state_at_step79=51,head_at_step79=5,one_cells_at_step79=[-3,-2],ray_start_step=85,ray_state=35,ray_head=7,ray_transition=[1,1,35],one_cells_at_ray_start=[-3,-2],all_other_cells=0,induction='After85+k steps: q=35, head=7+k, ones={-3,-2} union {7,...,6+k}.',consequence='This exact218-state table does not initialize the source from blank; its blank nonhalting has an elementary unconditional proof.')
 # Deterministic graph relabeling; no reachability-on-blank claim is inferred.
 order=[0];mp={0:0}
 for q in order:
  for b in(0,1):
   z=new[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
 assert set(mp)==Q;mp[254]=218
 can={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in new.items()}
 x.output.mkdir(parents=True,exist_ok=True)
 (x.output/'core218.native.tm').write_bytes(raw(new));(x.output/'core218.tm').write_bytes(raw(can));(x.output/'sites219.json').write_bytes(x.sites.read_bytes())
 put(x.output/'blank_failure.json',failure);put(x.output/'blank_first85.json',tr)
 receipt=dict(status='INITIALIZED_CORE_CONSTRUCTION_AND_DECODER_PASS_BLANK_FAILURE_PROVED',working_states=218,transition_rows=436,native_start=0,native_dispatch=84,native_halt=254,canonical_dispatch=mp[84],canonical_halt=218,table_sha256=CORE_SHA,canonical_sha256=sha(x.output/'core218.tm'),source_sha256=SOURCE_SHA,parent_sha256=BASE_SHA,removed_state=301,changed_retained_rows=[dict(state=q,read=b,old=old[q,b],new=new[q,b])for q,b in sorted(new)if old[q,b]!=new[q,b]],source_prefixes=4743,old_decoder_states=169,new_decoder_states=168,old301_paths=paths[301],old88_paths=paths[88],prefix_extra_steps=dict(timing),local_lemmas=lemmas,native_to_canonical=mp,blank_failure=failure,scope='Initialized-tape core only. The complete universal primitive proof is separate. No218-state blank-tape Con(ZFC) candidate is certified.')
 put(x.output/'construction.json',receipt);print(receipt['status'])
if __name__=='__main__':main()
