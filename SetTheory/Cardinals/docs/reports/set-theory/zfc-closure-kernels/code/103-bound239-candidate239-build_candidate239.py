"""Rebuild, canonically relabel, and independently check the 239-state candidate.

Standard library only. This script checks literal construction, a four-case
whole-tape block proof, incoming-edge tags, and the exact finite blank prefix.
The separate quantified source-runtime checker proves the register simulation.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,sys

if not __debug__ or sys.flags.optimize:
 raise RuntimeError('Run this certificate checker without Python -O or -OO.')

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
START,DISPATCH,HALT=95,96,254
EXPECTED_PROVISIONAL='a810ad476842b2e5bd49bafa6c89dc999cbfd8df72c17bc0866339ba7e27ecf4'
EXPECTED_FINAL='d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
PHY=(6,2,0,4,3,7,8,5,1)

def digest(data):return hashlib.sha256(data).hexdigest()
def read_table(path):
 table={};start=None
 for line in path.read_text().splitlines():
  if not line:continue
  if line.startswith('#! start '):start=int(line.split()[-1]);continue
  if line.startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
  assert (q,b) not in table and b in(0,1) and w in(0,1) and d in('L','R')
  table[q,b]=(w,d,t)
 assert start is not None
 return table,start

def encode(table,start):
 return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items()))).encode()
def changes(before,after):
 return [dict(state=q,read=b,old=before.get((q,b)),new=after.get((q,b))) for q,b in sorted(set(before)|set(after)) if before.get((q,b))!=after.get((q,b))]
def incoming(table,target):
 return [dict(state=q,read=b,write=w,move=d,target=t) for (q,b),(w,d,t) in sorted(table.items()) if t==target]
def write_json(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')

provisional_path=ROOT/'source_encoding/boundary239_provisional2_old.tm'
assert digest(provisional_path.read_bytes())==EXPECTED_PROVISIONAL
provisional,start=read_table(provisional_path);assert start==START and len(provisional)==478
assert 223 not in {q for q,b in provisional}
assert provisional[237,0]==(0,'R',218)
fork=dict(provisional);fork[237,0]=(0,'R',223)
fork[223,0]=(0,'R',23);fork[223,1]=(1,'R',70)
assert len(fork)==480
fork_bytes=encode(fork,START)
(HERE/'reference240_old.tm').write_bytes(fork_bytes)

# Every ordinary entry fixes the left cell before the state is entered.
tags={179:0,218:1,223:0}
incoming_checks={}
for q,bit in tags.items():
 rows=incoming(fork,q);assert rows and q!=START
 assert all(e['write']==bit and e['move']=='R' for e in rows)
 incoming_checks[q]=dict(required_left_bit=bit,all_incoming_rows=rows)

candidate={(179 if q==218 else q,b):(w,d,179 if t==218 else t) for (q,b),(w,d,t) in fork.items() if q!=218}
candidate[179,0]=(0,'R',105);candidate[179,1]=(1,'L',215)
assert len(candidate)==478
# The discovery table omits comments; preserve its exact published byte hash.
literal=encode(candidate,START).split(b'\n',1)[1];assert digest(literal)==EXPECTED_FINAL
(HERE/'zfc_boundary239_old.tm').write_bytes(literal)

# Four exact local cases suffice because the incoming tags are inductive.
# The simulator refuses to read any cell outside {-1,0}; such a case would
# require an additional hypothesis about the surrounding infinite tape.
def local_block(table,q,left,read,target,bound=32):
 h=0;cells={-1:left,0:read};initial=dict(cells);trace=[]
 for step in range(bound):
  if q==target and h==1:
   assert cells==initial
   return dict(steps=step,trace=trace,endpoint_state=q,endpoint_head=h,
               complete_tape_unchanged=True,read_positions=sorted({x['head'] for x in trace}))
  assert h in(-1,0),('Unexpected exterior tape read',q,h)
  b=cells[h];w,d,n=table[q,b]
  trace.append(dict(state=q,head=h,read=b,write=w,move=d,target=n))
  cells[h]=w;h+=1 if d=='R' else -1;q=n
 raise AssertionError('Local path did not finish')
blocks=[]
for old,left in[(179,0),(218,1)]:
 for read in(0,1):
  target=70 if old==218 and read==1 else 105
  blocks.append(dict(old_state=old,left_bit=left,read=read,
                     old=local_block(fork,old,left,read,target),
                     new=local_block(candidate,179,left,read,target)))

states={q for q,b in candidate};assert len(states)==239
assert set(candidate)=={(q,b) for q in states for b in(0,1)}
assert {t for w,d,t in candidate.values()}-states=={HALT}
order=[START]+sorted(states-{START});mapping={q:i for i,q in enumerate(order)}|{HALT:239}
canonical={(mapping[q],b):(w,d,mapping[t]) for(q,b),(w,d,t) in candidate.items()}
assert set(canonical)=={(q,b) for q in range(239) for b in(0,1)}
canonical_bytes=encode(canonical,0);(HERE/'zfc_boundary239.tm').write_bytes(canonical_bytes)
again,again_start=read_table(HERE/'zfc_boundary239.tm');assert again==canonical and again_start==0
for(q,b),(w,d,t)in candidate.items():assert again[mapping[q],b]==(w,d,mapping[t])
reached=set();todo=[START]
while todo:
 q=todo.pop()
 if q in reached:continue
 reached.add(q)
 if q!=HALT:todo.extend(candidate[q,b][2] for b in(0,1))
assert reached==states|{HALT}
write_json('renumbering.json',dict(old_to_new=mapping,new_to_old=order+[HALT],start_old=START,start_new=0,halt_old=HALT,halt_new=239))

# Sparse and dense interpreters use independent tape representations.
STEPS=409691
def sparse(table,start,steps):
 q,h,ones=start,0,set();used=Counter();minimum=maximum=0
 for tick in range(steps):
  read=int(h in ones);used[q,read]+=1;write,move,target=table[q,read]
  if write:ones.add(h)
  else:ones.discard(h)
  h+=1 if move=='R' else -1;q=target;minimum=min(minimum,h);maximum=max(maximum,h)
 return q,h,sorted(ones),used,(minimum,maximum)
def dense(table,start,steps):
 offset=steps+1;tape=bytearray(2*steps+3);position=offset;q=start
 for tick in range(steps):
  write,move,target=table[q,tape[position]];tape[position]=write
  position+=1 if move=='R' else -1;q=target
 return q,position-offset,[i-offset for i,b in enumerate(tape) if b]
base,base_start=read_table(ROOT/'baseline/rotation240/zfc_rotation240_old.tm')
a=sparse(base,base_start,STEPS);b=sparse(candidate,START,STEPS);c=dense(candidate,START,STEPS);d=dense(canonical,0,STEPS)
assert a[:3]==b[:3]==c and d==(mapping[c[0]],c[1],c[2])
q,head,ones=c;assert(q,head,len(ones))==(DISPATCH,-5,351)
assert all(b[3][key]==0 for key in b[3] if key[0]in(179,218,223,237))
on=set(ones);assert min(on)==head-1;header=min(x for x in on if x>=head)
values=[];position=header+1
while position<=max(on):
 assert position not in on and position+1 in on
 start=position+1;position=start
 while position in on:position+=1
 values.append(position-start-1)
logical=[values[i] for i in PHY]
assert logical==[3,0,0,0,3,0,0,0,0] and len(values[9:])==167 and set(values[9:])=={1}
write_json('blank_prefix.json',dict(status='EXACT_SPARSE_DENSE_AND_CANONICAL_AGREEMENT',steps=STEPS,
 initial_state=0,initial_head=0,initial_tape='all zero',final_state=mapping[DISPATCH],final_state_old=DISPATCH,
 final_head=head,marker=head-1,header=header,header_distance=header-head,pc='',
 logical_registers=logical,physical_registers=values[:9],spare_values=values[9:],
 all_one_positions=ones,all_other_cells_zero=True,one_count=len(ones),head_range=b[4],
 agrees_with_inherited_rotation240_complete_configuration=True,
 merged_or_split_states_seen_during_prefix=False))

root_reference,root_start=read_table(ROOT/'boundary240/boundary240_old.tm')
assert root_start==START
write_json('changes.json',dict(from_provisional239=changes(provisional,candidate),
 from_reference240=changes(fork,candidate),
 from_root_validated_boundary240_to_reference240=changes(root_reference,fork),
 from_inherited_rotation240=changes(base,candidate)))
write_json('incoming_and_blocks.json',dict(status='PASS',
 scope='Four exact whole-tape local blocks, under globally inductive incoming tags',
 initial_state_avoids_tagged_states=True,incoming_checks=incoming_checks,blocks=blocks,
 state_map={'218':179,'all_other_states':'identity'},
 proof_argument='All unchanged source-state transitions map identically. At a merged state, the tag fixes its old identity and one of the four positive finite blocks applies. No block reads exterior tape, no block changes any tape cell, and endpoints agree including head position. Therefore the fork240 and final239 machines have equivalent halting behavior from the common initial state on every tape.'))
canonical_sites_path=ROOT/'formalism/extra/boundary224_sites.json'
site_bytes=canonical_sites_path.read_bytes()
assert digest(site_bytes)=='7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
assert json.loads(site_bytes)==json.loads((ROOT/'source_encoding/boundary239_sites.json').read_bytes())
(HERE/'sites_logical.json').write_bytes(site_bytes)
result=dict(status='PASS',working_states=239,halt_states=1,rows=478,binary_symbols=[0,1],
 moves=['L','R'],start=0,halt=239,dispatch=mapping[DISPATCH],all_working_states_graph_reachable=True,
 inherited_label_sha256=digest(literal),canonical_sha256=digest(canonical_bytes),
 reference240_sha256=digest(fork_bytes),provisional239_sha256=EXPECTED_PROVISIONAL,
 source_sites_sha256=digest(site_bytes),canonical_action_isomorphism=True,
 exact_blank_prefix_steps=STEPS,local_block_cases=4,universal_runtime_proof='See universal_runtime.json; not performed by this script.')
write_json('literal_checks.json',result)
write_json('provenance.json',dict(construction='Boundary-aware source reparenthesization; explicit PUSH+1 decoder; left-tag fold179/218',
 inputs=[dict(path=str(p.relative_to(ROOT)),sha256=digest(p.read_bytes())) for p in[provisional_path,ROOT/'baseline/rotation240/zfc_rotation240_old.tm',ROOT/'boundary240/boundary240_old.tm',canonical_sites_path]],
 generated_files=[dict(path=p.name,sha256=digest(p.read_bytes())) for p in[HERE/'reference240_old.tm',HERE/'zfc_boundary239_old.tm',HERE/'zfc_boundary239.tm',HERE/'sites_logical.json']],
 detailed_row_changes='changes.json',exact_label_map='renumbering.json',
 separation_of_obligations='Literal checks and block proof here; source CFG equivalence and quantified source-runtime semantics are separate certificates in the package.'))
print(json.dumps(result,indent=2))
