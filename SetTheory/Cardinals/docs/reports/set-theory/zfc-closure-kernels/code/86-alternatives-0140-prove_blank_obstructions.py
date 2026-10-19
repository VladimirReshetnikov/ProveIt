#!/usr/bin/env python3
"""Literal finite certificates plus elementary induction for both failed starts."""
import json,hashlib
from pathlib import Path
from explore import T
HERE=Path(__file__).resolve().parent
out={}
for borrow in[33,126]:
 table=T|{(75,0):(0,1,63),(48,0):(1,-1,131),(131,0):(1,-1,borrow)}
 del table[255,0];del table[255,1]
 q,h,ones=95,0,set();seen={};trace=[]
 for step in range(10000):
  config=(q,h,tuple(sorted(ones)))
  assert q!=254
  if borrow==33 and q==42 and all(p<h for p in ones):
   assert table[42,0]==(1,1,42)
   out[str(borrow)]=dict(status='PROVED_NONHALTING_FROM_BLANK',method='Rightward blank-ray induction',entry_step=step,entry=dict(state=q,head=h,ones=sorted(ones)),row=[42,0,1,'R',42],induction='For every n>=0, state42 is at entry_head+n, with the initial support plus all cells from entry_head through entry_head+n-1 equal to1. The scanned cell and every cell to its right are0. The next literal row preserves this claim, so halt254 is never reached.',prefix_trace=trace);break
  if config in seen:
   first=seen[config]
   out[str(borrow)]=dict(status='PROVED_NONHALTING_FROM_BLANK',method='Exact whole-configuration cycle',first_step=first,repeat_step=step,period=step-first,repeated_configuration=dict(state=q,head=h,ones=sorted(ones)),induction='The complete finite support, state, and head are identical at both boundaries. Determinism repeats the intervening nonhalting cycle indefinitely.',prefix_and_cycle_trace=trace);break
  seen[config]=step
  read=int(h in ones);w,d,nq=table[q,read]
  trace.append(dict(step=step,state=q,head=h,read=read,write=w,move='R'if d==1 else'L',next=nq))
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;q=nq
 else:raise AssertionError('certificate did not close')
 out[str(borrow)]['working_states']=len(table)//2
 out[str(borrow)]['claim_scope']='This proves failure of these exact unmodified blank starts as proof-search implementations. It is not a lower bound or an obstruction to different counter rows and a corrected bootstrap.'
(HERE/'blank_obstructions.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({q:{k:v for k,v in data.items()if 'trace'not in k}for q,data in out.items()},indent=2))
