#!/usr/bin/env python3
"""Portable bounded replay failures for two rejected rotation-fold allocations.

This reproduces two failures to meet the exact expected macro frame within
the stated finite limit. It does not establish unbounded non-equivalence.
"""
from pathlib import Path
from collections import defaultdict
import json,hashlib
HERE=Path(__file__).resolve().parent
def need(p,msg):
 if not p:raise ValueError(msg)
def table():
 t={}
 for line in (HERE/'rejected207.native.tm').read_text().splitlines():
  if line.startswith('#') or not line:continue
  q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 need(len(t)==414,'table does not have 207 complete states')
 return t
def frame(p,regs=None,gap=0):
 regs=[0]*9 if regs is None else regs
 tape=defaultdict(int);tape[-1]=1;tape[56+gap]=1
 for i,b in enumerate(p):tape[i]=int(b)
 physical=[6,2,0,4,3,7,8,5,1];values=[0]*9
 for i,x in enumerate(regs):values[physical[i]]=x
 values.append(0);cursor=57+gap
 for value in values:
  for j in range(1,value+2):tape[cursor+j]=1
  cursor+=value+2
 return tape
def run(t,rows,ordinal,positive=False):
 p,op,arg=rows[ordinal];need(op=='CD','witness must be a decrement')
 regs=[0]*9;regs[arg]=int(positive)
 prefix=p if positive else p[:p.rfind('0')]
 expected_pc=format((int(prefix,2)+1)%(1<<len(prefix)),f'0{len(prefix)}b')
 expected=frame(expected_pc,gap=int(positive));tape=frame(p,regs);q=84;h=0;trace=[]
 for tick in range(10000):
  if tick and q==84:break
  need(q!=254,'unexpected halt before dispatcher return')
  b=tape[h];w,d,z=t[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
 else:raise ValueError('no dispatcher return')
 expected_ordinal=next(i for i,(addr,_,_) in enumerate(rows) if (expected_pc+'0'*60).startswith(addr))
 actual_pc=''.join(str(tape[i]) for i in range(60))
 actual_ordinal=next(i for i,(addr,_,_) in enumerate(rows) if actual_pc.startswith(addr))
 mismatch=[i for i in sorted(set(tape)|set(expected)) if tape[i]!=expected[i]]
 need(mismatch or h!=0,'witness unexpectedly passes')
 # Optional stronger evidence: look for an exact repeated full configuration.
 initial=frame(p,regs);ones=sum(1<<(i+256) for i,v in initial.items() if v);expected_ones=sum(1<<(i+256) for i,v in expected.items() if v)
 seen={};cq=84;ch=0;cycle=None
 for n in range(100000):
  signature=(cq,ch,ones)
  need(not(n and cq==84 and ch==0 and ones==expected_ones),'eventual expected return found')
  if signature in seen:
   cycle={'first_occurrence':seen[signature],'second_occurrence':n,'period':n-seen[signature]};break
  seen[signature]=n;need(-256<=ch<3840,'cycle trace leaves encoded tape');need(cq!=254,'cycle trace halts')
  bit=(ones>>(ch+256))&1;w,d,z=t[cq,bit]
  ones=(ones&~(1<<(ch+256)))|(w<<(ch+256));ch+=d;cq=z
 return {'input_ordinal':ordinal,'instruction':[op,arg],'address':p,'guard':'positive' if positive else 'zero','registers':regs,'spares':[0],'gap':0,
  'literal_steps_to_first_dispatcher_return':len(trace),'return_head':h,'expected_ordinal':expected_ordinal,
  'actual_ordinal':actual_ordinal,'differing_tape_positions':mismatch,'exact_nonhalting_cycle':cycle,'no_expected_return_in_first_100000_steps':True,'trace':trace}
rows=json.loads((HERE/'sites.json').read_text());t=table()
base=run(t,rows,25)
patched=dict(t);patched[152,0]=(0,-1,133);repair=run(patched,rows,70,positive=True)
out={'status':'REJECTED_FINITE_REPLAY','table_sha256':hashlib.sha256((HERE/'rejected207.native.tm').read_bytes()).hexdigest(),
 'unmodified_rotation_fold':base,'attempted_repair':{'patch':{'state':152,'read':0,'old':[0,-1,159],'new':[0,-1,133]},'witness':repair},
 'scope':'The first dispatcher return is diagnostic only: it need not be a macro endpoint. Neither failed input attains its exact expected macro frame within 100000 literal steps. No unbounded non-equivalence or blank-halting inequivalence is claimed.'}
(HERE/'counterexamples.json').write_text(json.dumps(out,indent=2)+'\n')
for label,w in [('unrepaired',base),('one-row repair',repair)]:
 print(label, 'input',w['input_ordinal'],'steps',w['literal_steps_to_first_dispatcher_return'],'expected',w['expected_ordinal'],'actual',w['actual_ordinal'],'head',w['return_head'])
