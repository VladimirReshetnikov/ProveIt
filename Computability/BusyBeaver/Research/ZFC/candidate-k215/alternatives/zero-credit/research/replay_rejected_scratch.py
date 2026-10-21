#!/usr/bin/env python3
"""Independent exact source-CFG and false-halt audit of archived scratch-biased215.
This rejects its claimed parser interface; physical primitive verification is separate.
"""
from pathlib import Path
import json,hashlib,sys,argparse,tempfile
RROOT=Path(__file__).resolve().parent/'rejected_scratch_transfer'
source=RROOT/'source.sites.json'
machine=RROOT/'machine.native.tm'
rows=json.loads(source.read_text());N=len(rows)
# Construct tree intervals independently, then resolve control through ancestor cuts.
intervals={}
for ordinal,(p,op,a)in enumerate(rows):
 for n in range(len(p)+1):
  if p[:n]not in intervals:intervals[p[:n]]=[ordinal,ordinal+1]
  else:intervals[p[:n]][1]=ordinal+1

def edges(i):
 p,op,a=rows[i]
 if op=='CH':return []
 if op=='CI':return[(i+1)%N]
 symbol='0'if op in('CD','CB')else'1';d=1 if op=='CD'else a
 for j in range(len(p)-1,-1,-1):
  if p[j]==symbol:
   d-=1
   if d==0:
    target=intervals[p[:j]][int(symbol=='0')]%N;break
 else:target=0
 return[target,(i+1)%N]if op=='CD'else[target]
assert rows[4696]==['100110','CI',6]
assert rows[4697]==['100111','CC',3]
assert edges(4697)==[23]

def source_run(start):
 regs=[1,0,0,0,0,0,0,0,0];pc=start;trace=[]
 for k in range(100):
  trace.append({'step':k,'pc':pc,'registers':regs.copy()})
  op,a=rows[pc][1:];es=edges(pc)
  if op=='CH':return trace
  if op=='CI':regs[a]+=1;pc=es[0]
  elif op=='CD':b=regs[a]>0;regs[a]-=int(b);pc=es[int(b)]
  else:pc=es[0]
 raise AssertionError('Finite witness did not halt')
suffix=source_run(4696);mp=source_run(4590)
assert len(suffix)-1==15 and suffix[-1]['pc']==4718
assert len(mp)-1==40 and mp[-1]['pc']==4718
# Independently replay literal binary rows from the matching safe MP entry frame.
T={}
for line in machine.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();key=int(q),int(b);assert key not in T
 T[key]=int(w),1 if d=='R'else-1,int(z)
PHY=(6,2,0,4,3,7,8,5,1)
regs=[1,0,0,0,0,0,0,0,0];values=[0]*9
for i,j in enumerate(PHY):values[j]=regs[i]
pc=rows[4590][0];ones={-1,64}|{i for i,b in enumerate(pc)if b=='1'};p=65
for v in values+[0]:
 p+=1;ones.update(range(p,p+v+1));p+=v+1
initial=sorted(ones);q=84;h=0;hh=hashlib.sha256()
for k in range(1000000):
 if q==254:break
 b=int(h in ones);w,d,z=T[q,b]
 hh.update(f'{q} {h} {b} {w} {d} {z}\n'.encode())
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;q=z
else:raise AssertionError('Literal binary witness did not halt')
report={'status':'CLAIMED_PARSER_INTERFACE_FALSIFIED','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'table_sha256':hashlib.sha256(machine.read_bytes()).hexdigest(),'return_leaf':rows[4697],'actual_return_ordinal':23,'claimed_return_ordinal':0,'return_reason':'CC3 removes the last three one-ancestors of100111, leaving100. That prefix starts at23. The pre-insertion address10011 had only three ones and returned0.','suffix_primitive_steps':15,'zero_MP_primitive_steps':40,'halt_ordinal':4718,'suffix_trace':suffix,'mp_trace':mp,'binary_witness':{'start_state':84,'start_head':0,'start_pc':pc,'registers':regs,'spares':[0],'initial_ones':initial,'steps_to_halt':k,'halt_state':q,'halt_head':h,'final_ones':sorted(ones),'literal_transition_trace_sha256':hh.hexdigest()},'proof_scope':'Literal counterexample from a safe theorem frame: top/cache/stack code0. For actual blank halting, combine the separately checked partial-AX blank prefix, inherited total AX contract including A=H=X=Y=0, and the suffix lemma (the suffix never reads the stack).'}
parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path);args=parser.parse_args()
if args.out:args.out.write_text(json.dumps(report,indent=2)+'\n')
expected=json.loads((Path(__file__).parent/'scratch_transfer_audit.json').read_text());assert report==expected

print(json.dumps({k:v for k,v in report.items()if k not in('suffix_trace','mp_trace','binary_witness')},indent=2))
print('BINARY_HALT',report['binary_witness']['steps_to_halt'])
