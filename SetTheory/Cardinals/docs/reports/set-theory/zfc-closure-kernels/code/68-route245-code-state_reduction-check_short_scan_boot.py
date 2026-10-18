#!/usr/bin/env python3
"""Exact two-interpreter replay and local contraction audit for scanner deletion74.

No runtime or consistency claim: the unchanged source has a known runtime
counterexample to this scanner shortening.
"""
import argparse,hashlib,json
from pathlib import Path
P=argparse.ArgumentParser();P.add_argument('--table',type=Path,required=True);P.add_argument('--baseline-bootstrap',type=Path,required=True);P.add_argument('--output',type=Path,required=True);a=P.parse_args()
T={}
for line in a.table.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,t=line.split();T[int(q),int(b)]=int(w),1 if d=='R' else -1,int(t)
assert T[58,0]==(0,-1,74) and T[74,0]==(0,-1,84) and T[84,0]==(0,1,84)
old_steps=410735
q,h,ones=95,0,set();triples={};contractions=0
for _ in range(old_steps):
 b=int(h in ones)
 if(q,b)==(58,0):
  ctx=tuple(int(h-j in ones) for j in range(3));triples[ctx]=triples.get(ctx,0)+1
  assert ctx==(0,0,0)
  contractions+=1
 w,d,q=T[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
reference=json.loads(a.baseline_bootstrap.read_text())['old_labels']
assert(q,h,sorted(ones))==(96,-5,reference['all_one_positions'])
short=T.copy();short[58,0]=(0,-1,84);del short[74,0];del short[74,1]
assert all(t!=74 for w,d,t in short.values())
new_steps=old_steps-2*contractions
# Sparse replay of shortened table.
sq,sh,sones=95,0,set()
for _ in range(new_steps):
 w,d,sq=short[sq,int(sh in sones)]
 if w:sones.add(sh)
 else:sones.discard(sh)
 sh+=d
assert(sq,sh,sones)==(q,h,ones)
# Independent dense replay; rows and tape are arrays, not dictionaries or sets.
rows=[None]*(2*(1+max(q for q,b in short)))
for(state,bit),(write,delta,target)in short.items():rows[2*state+bit]=write,delta,target
origin=new_steps+1;tape=bytearray(2*new_steps+3);position,state=origin,95
for _ in range(new_steps):
 write,delta,target=rows[2*state+tape[position]]
 tape[position]=write;position+=delta;state=target
positions=[i-origin for i,b in enumerate(tape)if b]
assert(state,position-origin,positions)==(sq,sh,sorted(sones))
out=dict(status='PASS_FINITE_BOOT_AND_LOCAL_CONTRACTION_ONLY',baseline_table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),states_after_edit=len(short)//2,edit={'58/0':'0 L 84'},deleted_state=74,baseline_steps=old_steps,shortened_steps=new_steps,contractions=contractions,observed_context_counts=[dict(bits_at_x_xminus1_xminus2=list(k),count=v)for k,v in sorted(triples.items())],local_contraction='On tape(x)=tape(x-1)=tape(x-2)=0, original58/0;74/0;84/0 is exactly replaced by shortened58/0. Both end in84 atx-1 with unchanged tape; two moves saved.',independent_sparse_dense_agreement=True,endpoint=dict(state=sq,head=sh,one_count=len(sones),all_one_positions=sorted(sones)),scope='Finite bootstrap and a three-cell local rewrite only. The unchanged source has a known runtime counterexample; no below246 consistency machine is certified.')
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='endpoint'},indent=2))
