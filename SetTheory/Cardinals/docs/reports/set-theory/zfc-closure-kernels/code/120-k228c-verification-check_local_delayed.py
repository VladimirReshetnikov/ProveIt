#!/usr/bin/env python3
"""Independent literal local proof for the K140-to-K71 delayed-erasure fold.

A single premise, at old140 reading1 the right neighbor is1, is NOT inferred
from the control graph. The exact startup certificate checks this guard on
its finite trace. The direct candidate runtime certificate proves the whole
source-program contract without assuming or proving that global cross-machine
guard. This local conditional identity is explanatory, not the sole transfer
proof. No finite execution substitutes for an unbounded guard theorem.
"""
from pathlib import Path
import itertools,argparse,json,hashlib
import sys
if not __debug__ or sys.flags.optimize:
 raise RuntimeError('Assertions must be enabled.')

def parse(p):
 t={};start=None
 for line in Path(p).read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:])
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b) not in t and b in(0,1) and w in(0,1) and d in('L','R');t[q,b]=(w,1 if d=='R' else -1,z)
 qs={q for q,b in t};assert set(t)=={(q,b) for q in qs for b in(0,1)};assert{z for w,d,z in t.values()}-qs=={254};assert start==95
 return t

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--old',required=True);p.add_argument('--new',required=True);p.add_argument('--output',required=True);a=p.parse_args();old,new=map(parse,(a.old,a.new));phi=lambda q:71 if q==140 else q
assert len(new)==len(old)-2;assert{q for q,b in new}=={q for q,b in old}-{140}
arrivals={}
for q,v in((58,0),(71,1),(80,1),(140,0)):
 arr=[(p,b,w,d) for(p,b),(w,d,z) in old.items() if z==q];assert arr and all((w,d)==(v,1) for p,b,w,d in arr);arrivals[q]=arr
assert all(p==58 for p,b,w,d in arrivals[71]);assert all(p==71 for p,b,w,d in arrivals[80])
assert all(new[q,b]==(w,d,phi(z)) for(q,b),(w,d,z) in old.items() if(q,b) not in {(71,0),(140,0),(140,1),(80,1)})
specs=[(71,0,{-2:0,-1:1},5),(140,0,{-1:0},3),(140,1,{-1:0,1:1},5),(80,1,{-3:0,-2:1,-1:1},9)];proofs=[]
for q,b,guard,steps in specs:
 assignments=0;example=None
 for bits in itertools.product((0,1),repeat=5):
  before=dict(zip(range(-3,2),bits))
  if before[0]!=b or any(before[k]!=v for k,v in guard.items()):continue
  cells=before.copy();state=phi(q);head=0;trace=[]
  for tick in range(steps):
   assert head in cells,'Would read unrepresented exterior'
   rd=cells[head];w,d,z=new[state,rd];trace.append([state,head,rd,w,d,z]);cells[head]=w;head+=d;state=z;assert state!=254
  ow,od,oz=old[q,b];want={**before,0:ow};assert(state,head,cells)==(phi(oz),od,want),(q,b,before,trace)
  assignments+=1;example=trace
 assert assignments
 proofs.append({'row':[q,b],'guard':guard,'duration':steps,'boolean_assignments':assignments,'read_write_footprint':[-3,1],'representative_trace':example,'all_exterior_cells_unread_and_unchanged':True})
out={'status':'CONDITIONAL_ALL_TAPE_LOCAL_BLOCK_PROOF_PASS','old_sha256':sha(a.old),'new_sha256':sha(a.new),'deleted_state':140,'retained_state':71,'incoming_inventory':arrivals,'ordinary_rows':len(old)-4,'exceptional_rows':4,'proofs':proofs,'additional_runtime_premise':'At old state140 reading1, tape(head+1)=1. Must hold at every relevant checkpoint, beyond the control-graph invariant.','scope':'Every old step has a positive new block (1,3,5,or9steps), all tape cells preserved as required, provided the displayed invariant and additional runtime premise hold. This checker alone does not prove blank-halting equivalence.'}
Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='proofs'},indent=2))
