from pathlib import Path
import sys,json,importlib.util
sys.path.insert(0,str(Path(__file__).resolve().parent));import repair_rotation as r
m=r.m
p=m.FROZEN/'code/check_literal_instructions.py'
spec=importlib.util.spec_from_file_location('literal',p);lit=importlib.util.module_from_spec(spec);spec.loader.exec_module(lit)
pc='11101001001010100111000000';regs=[1,0,0,0,0,0,0,0,0];spares=[1];start_head=0;span=40
expected=lit.expected(pc,'CD',1,regs,spares,start_head,span)
records={}
for name,tt in [('baseline246',m.T),('rotation178_245',r.tt)]:
 one=lit.paint(pc,span,regs,spares,start_head);q=96;head=start_head;trace=[];boundaries=[]
 for steps in range(1,100001):
  b=int(head in one);w,d,t=tt[q,b]
  if len(trace)<80:trace.append([steps,q,head,b,w,d,t])
  if w:one.add(head)
  else:one.discard(head)
  head += 1 if d=='R' else -1;q=t
  if q in (96,254):
   rec=dict(steps=steps,state=q,head=head,ones=sorted(one),matches_expected=(q==96 and head==expected[0] and one==expected[1]))
   boundaries.append(rec)
   if rec['matches_expected'] or len(boundaries)>=3 or q==254:
    records[name]=dict(**rec,boundaries=boundaries,trace_first80=trace);break
 else:raise AssertionError('fuel')
result=dict(status='DIFFERENT_THIRD_DISPATCHER_TAPE',not_a_blank_run_counterexample=True,not_a_halting_language_counterexample=True,intermediate_dispatches_retained=True,pc=pc,source_operation=['EDecnz',1],guard=['physical_register',2,'zero'],physical_registers=regs,spares=spares,head=start_head,header_distance=span,initial_ones=sorted(lit.paint(pc,span,regs,spares,start_head)),expected=dict(head=expected[0],ones=sorted(expected[1]),next_pc=expected[2],header_distance=expected[3],physical_registers=expected[4],spares=expected[5]),runs=records)
assert records['baseline246']['matches_expected']
assert not records['rotation178_245']['matches_expected']
actual_pc='11101001001010100111000001'
assert records['rotation178_245']['ones']==sorted(lit.paint(actual_pc,span,regs,spares,start_head))
result['rotated_third_dispatch']=dict(pc=actual_pc,physical_registers=regs,spares=spares,header_distance=span,head=start_head)
result['interpretation']='The intended one-source-instruction dispatcher target is reached by baseline246 after 380 literal steps. After 378 steps the rotated table instead reaches an ordinary encoded dispatcher configuration with unchanged registers and a different program counter. The first two dispatcher visits are transient and are explicitly shown. This finite trace is not a claim about the machine halting language or blank run.'
(m.HERE/'rotation_candidates/rotation178_literal_counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
for k,v in records.items():print(k,{a:b for a,b in v.items()if a not in ('trace_first80','ones','boundaries')},'ones',v['ones'])
print('expected',result['expected'])
