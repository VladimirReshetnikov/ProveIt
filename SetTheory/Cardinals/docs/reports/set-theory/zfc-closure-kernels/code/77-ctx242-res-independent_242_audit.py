#!/usr/bin/env python3
"""Independent finite schema audit for the contextual 243 -> 242 fold.

This is an executable check of the finite premises of the ordinary proof,
not a proof-assistant certificate. Local windows are universally quantified:
every run below reads only coordinates represented in the window and leaves
the arbitrary exterior untouched.
"""
from pathlib import Path
import hashlib,itertools,json

BASE=Path(__file__).resolve().parents[1]/'reference/combined243/zfc_combined243_old.tm'
EXPECTED='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()==EXPECTED
old={}
for line in BASE.read_text().splitlines():
 if line.startswith('#') or not line.strip():continue
 q,b,w,d,t=line.split(); key=int(q),int(b)
 assert key not in old
 old[key]=(int(w),d,int(t))
new=dict(old)
for q in (18,47,65):
 assert old[q,0]==(0,'L',27)
 new[q,0]=(0,'L',15)
assert old[15,0]==(0,'R',21)
new[15,0]=(0,'L',32)
del new[27,0],new[27,1]
states={q for q,b in new}
assert len(states)==242 and set(new)=={(q,b) for q in states for b in (0,1)}
assert {q for _,_,q in new.values()}-states=={254}
assert {k for k in new if new[k]!=old[k]}=={(15,0),(18,0),(47,0),(65,0)}

guard_states={15,18,47,65}
incoming={q:[] for q in guard_states}
for (q,b),(w,d,t) in old.items():
 if t in guard_states:
  assert (w,d)==(0,'R')
  incoming[t].append([q,b,w,d,t])
assert 95 not in guard_states
assert {(q,b) for (q,b),(_,_,t) in old.items() if t==27}=={(18,0),(47,0),(65,0)}

def execute(table,q,cells,n):
 h=0;cells=dict(cells);trace=[]
 for _ in range(n):
  assert h in cells,'Read outside universally enumerated window'
  b=cells[h];w,d,t=table[q,b]
  trace.append([q,h,b,w,d,t]);cells[h]=w
  h+=1 if d=='R' else -1;q=t
 return (q,h,cells),trace

blocks=[]
for q,na,nb in [(15,1,3),(18,2,2),(47,2,2),(65,2,2)]:
 count=0;example=None
 for bits in itertools.product((0,1),repeat=5):
  cells=dict(zip(range(-2,3),bits))
  if cells[0] or cells[-1]:continue
  a,ta=execute(old,q,cells,na)
  b,tb=execute(new,q,cells,nb)
  assert a==b and a[0]!=27
  assert all(step[-1]!=254 for step in ta+tb)
  count+=1;example={'old':ta,'new':tb,'endpoint_state':a[0],'head':a[1]}
 blocks.append({'entry':q,'guard':'read=0 and left=0','old_steps':na,'new_steps':nb,
                'all_local_windows':count,'example':example})

exceptional={(15,0),(18,0),(47,0),(65,0)}
ordinary=0
for key,value in new.items():
 if key in exceptional:continue
 assert old[key]==value and value[2]!=27
 ordinary+=1
assert ordinary==480

record={'status':'PASS_FINITE_PREMISES_FOR_UNIVERSAL_BLOCK_SIMULATION',
 'source_sha256':EXPECTED,'working_states':242,'binary_rows':484,
 'deleted_old_state':27,'changed_retained_rows':[[q,b,*new[q,b]] for q,b in sorted(exceptional)],
 'old_invariant':'State in {15,18,47,65} implies tape(head-1)=0',
 'old_invariant_incoming_edges':{str(k):v for k,v in sorted(incoming.items())},
 'initial_invariant':'Vacuous at state95 for every head and every binary tape',
 'blocks':blocks,'ordinary_equal_rows':ordinary,
 'conclusion':'Old and new halt equivalently from state95, any head, any tape; follows by positive complete-configuration blocks.',
 'proof_status':'Independent ordinary proof-premise checker; no Lean/Rocq claim.'}
out=Path(__file__).resolve().parents[1]/'evidence/independent_242_audit.json'
out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
