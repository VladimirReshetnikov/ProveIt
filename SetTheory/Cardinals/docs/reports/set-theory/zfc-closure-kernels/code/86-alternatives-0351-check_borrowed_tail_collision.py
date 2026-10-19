#!/usr/bin/env python3
"""Exact finite transition proof of a pre126 collision; no halting inference."""
from pathlib import Path
import sys,json,hashlib
H=Path(__file__).resolve().parent;B=H.parent/'context_folds/recovered/63';sys.path.insert(0,str(B/'code'))
import check_literal_instructions as l
t=l.read_table(B/'machine/zfc_prefix246_old.tm');del t[255,0];del t[255,1];t[75,0]=(0,1,63);t[48,0]=(1,-1,131);t[131,0]=(1,-1,126)
inputs=[('11101001001000010110',6),('11101001001000101010',1)];results=[]
for pc,r in inputs:
 regs=[1]*9;regs[l.PHYSICAL[r]]=0;one=l.paint(pc,40,regs,[1],0);q,h=96,0;trace=[]
 for steps in range(20000):
  if q==126 and h not in one:break
  key=q,int(h in one);assert key!=(108,0),'A repair at108 could affect this witness'
  w,d,qq=t[key];trace.append([q,h,int(h in one),w,d,qq]);one.add(h)if w else one.discard(h);q=qq;h+=d
 else:raise AssertionError('boundary not reached')
 target_pc=l.add_one(pc);target_regs=[1]*9;target_one=l.paint(target_pc,40,target_regs,[0,1],0)
 results.append(dict(pc=pc,logical_register=r,initial_physical_registers=regs,initial_spares=[1],boundary_steps=steps,boundary_state=q,boundary_head=h,boundary_ones=sorted(one),desired_pc=target_pc,desired_head=0,desired_ones=sorted(target_one),trace=trace))
a,b=results;assert(a['boundary_state'],a['boundary_head'],a['boundary_ones'])==(b['boundary_state'],b['boundary_head'],b['boundary_ones']);assert a['desired_ones']!=b['desired_ones']
report=dict(status='EXACT_PRE126_COLLISION',interpretation='Distinct valid instruction interfaces reach identical physical configuration before reading either free126/0 or repaired108/0, but their required next-PC frames differ. This proves information loss in the proposed fixed arithmetic prefix; it does not prove impossibility of arbitrary future code or alternate simulation relations.',fixed_edits={'75/0':[0,'R',63],'48/0':[1,'L',131],'131/0':[1,'L',126]},removed=[255],witnesses=results)
(H/'borrowed_tail_exact_collision.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='witnesses'},indent=2));print([(x['boundary_steps'],x['boundary_head'],x['desired_pc'])for x in results])
