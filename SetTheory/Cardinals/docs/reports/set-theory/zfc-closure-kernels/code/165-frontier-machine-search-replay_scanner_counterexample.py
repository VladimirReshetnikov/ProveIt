#!/usr/bin/env python3
"""Replay a concrete contract failure of the rejected 214-state scanner."""
from pathlib import Path
import argparse,hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
def main():
 p=argparse.ArgumentParser();p.add_argument('--baseline',type=Path,default=HERE.parent/'baseline/k215')
 p.add_argument('--out',type=Path,default=HERE/'rejected/scanner214_counterexample.json');a=p.parse_args()
 s=importlib.util.spec_from_file_location('ir',a.baseline/'code/runtime-inputs/runtime/independent_runtime.py')
 ir=importlib.util.module_from_spec(s);s.loader.exec_module(ir)
 site_index=26;site=json.loads((HERE/'accepted/original_sites.json').read_text())[site_index]
 assert site==['1101001001000000','CD',1]
 regs=[0]*9;initial=ir.frame(site[0],regs,[0],0)
 expected=ir.expected(site,regs,[0],0);want=(84,expected[0][1],expected[0][2])
 def run(path):
  T=ir.table(path);q,h=84,0;ones=set(initial);trace=[]
  for tick in range(100000):
   if tick and (q==254 or ir.clean_dispatch(96 if q==84 else -1,h,ones)):
    return (q,h,ones),trace
   bit=int(h in ones);w,d,z=T[q,bit];trace.append([tick,q,h,bit,w,d,z])
   if w:ones.add(h)
   else:ones.discard(h)
   h+=d;q=z
  raise RuntimeError('Bound exhausted')
 original,original_trace=run(HERE/'accepted/original215.native.tm')
 actual,trace=run(HERE/'rejected/scanner214.native.tm')
 assert original==want and actual!=want
 assert actual[0]==84 and actual[1]==0
 assert sorted(actual[2]^want[2])==[12,14]
 def desc(c):return {'state':c[0],'head':c[1],'ones':sorted(c[2])}
 record={'status':'CONCRETE_RUNTIME_CONTRACT_COUNTEREXAMPLE',
  'scope':'Valid primitive-frame failure; not a blank-run nonhalting or equiconsistency claim.',
  'site_index':site_index,'site':site,'logical_registers':regs,'spares':[0],'gap':0,
  'start_state':84,'start_head':0,'initial_one_cells':sorted(initial),
  'expected':desc(want),'expected_logical':expected[1],'actual':desc(actual),
  'baseline_steps':len(original_trace),'candidate_steps':len(trace),
  'different_one_cells':[12,14],'native_state_labels':True,
  'table_sha256':hashlib.sha256((HERE/'rejected/scanner214.native.tm').read_bytes()).hexdigest(),
  'trace_format':['tick','state','head','read','write','direction','target'],'trace':trace}
 a.out.write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps({k:v for k,v in record.items() if k not in ['trace','initial_one_cells','expected','actual']},indent=2))
if __name__=='__main__':main()
