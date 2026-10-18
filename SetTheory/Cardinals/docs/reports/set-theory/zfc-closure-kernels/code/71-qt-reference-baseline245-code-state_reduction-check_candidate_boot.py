#!/usr/bin/env python3
"""Independent exact blank replay for a concrete old-label candidate table."""
import argparse,hashlib,json
from pathlib import Path
P=argparse.ArgumentParser();P.add_argument('--table',type=Path,required=True);P.add_argument('--steps',type=int,default=407915);P.add_argument('--baseline-bootstrap',type=Path,required=True);P.add_argument('--output',type=Path,required=True);a=P.parse_args();rows={};start=None
for line in a.table.read_text().splitlines():
 if not line:continue
 if line.startswith('#! start '):start=int(line.split()[-1]);continue
 if line.startswith('#'):continue
 q,b,w,d,t=line.split();rows[int(q),int(b)]=int(w),(-1 if d=='L'else 1),int(t)
assert start==95;states={q for q,b in rows};assert len(rows)==2*len(states) and 254 not in states
assert all(t in states or t==254 for w,d,t in rows.values())
# Sparse interpreter with set tape and dictionary transition lookup.
state,head,ones=start,0,set()
for _ in range(a.steps):
 write,delta,state=rows[state,int(head in ones)]
 if write:ones.add(head)
 else:ones.discard(head)
 head+=delta
# Dense interpreter with independent table construction and indexed tape.
flat=[None]*(2*(max(states)+1))
for(q,b),(w,d,t)in rows.items():flat[2*q+b]=w,d,t
origin=a.steps+1;position=origin;current=start;tape=bytearray(2*a.steps+3)
for _ in range(a.steps):
 w,d,t=flat[2*current+tape[position]];tape[position]=w;position+=d;current=t
allones=[i-origin for i,b in enumerate(tape)if b]
assert(current,position-origin,allones)==(state,head,sorted(ones))
expected=json.loads(a.baseline_bootstrap.read_text())['old_labels'];assert(state,head,allones)==(96,-5,expected['all_one_positions'])
header=176;assert header in ones and head-1 in ones;pos=header+1;values=[]
while pos<=max(ones):
 assert pos not in ones
 j=pos+1
 while j in ones:j+=1
 assert j>pos+1
 values.append(j-pos-2);pos=j
physical=values[:9];spares=values[9:];mapping=[6,2,0,4,3,7,8,5,1];logical=[physical[i]for i in mapping]
assert physical==[0,0,0,3,0,0,3,0,0]and spares==[1]*167
out=dict(status='PASS_EXACT_TWO_INTERPRETER_BOOT',table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),working_states=len(states),steps=a.steps,start=start,dispatcher=state,head=head,marker=head-1,header=header,header_distance=header-head,physical_registers=physical,logical_registers=logical,spare_count=len(spares),all_spares_equal_one=True,one_count=len(ones),all_one_positions=allones,independent_sparse_dense_agreement=True,all_other_cells_zero=True,scope='Exact finite blank initialization; separate instruction and source/logical proofs establish eventual-halting correspondence.')
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='all_one_positions'},indent=2))
