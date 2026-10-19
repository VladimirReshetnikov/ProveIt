#!/usr/bin/env python3
"""Exact sparse/dense refutation of the unchanged-caller integration."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
BASE=HERE/'reference/routing245_old.tm';CAND=HERE/'left_increment_local244_old.tm'
def read(path):
    table={};start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start'):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=int(q),int(b);assert key not in table
        table[key]=(int(w),1 if d=='R' else -1,int(t))
    return table,start
old,start=read(BASE);table,start2=read(CAND);assert start==start2==95
assert len(old)==490 and len(table)==488
expected=old.copy();expected[75,0]=(0,-1,112);expected[83,0]=(1,-1,112);expected[131,0]=(0,1,48)
del expected[255,0];del expected[255,1];assert table==expected
assert len({q for q,b in table})==244

def paint(pc,gap,regs,spares,head=0):
    out={head-1,head+gap};out.update(head+i for i,b in enumerate(pc) if b=='1');p=head+gap+1
    for v in regs+spares:
        out.update(range(p+1,p+v+2));p+=v+2
    return out

def sparse(t,initial,count):
    ones=initial.copy();q,h=96,0
    for i in range(count):
        w,d,q=t[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    return q,h,sorted(ones)
def dense(t,initial,count):
    lo=min(-count-2,min(initial)-2);hi=max(count+2,max(initial)+2);cells=bytearray(hi-lo+1)
    for p in initial:cells[p-lo]=1
    q,h=96,-lo
    for i in range(count):
        w,d,q=t[q,cells[h]];cells[h]=w;h+=d
    return q,h+lo,[i+lo for i,b in enumerate(cells) if b]

regs=[6,3,3,5,0,0,0,1,4];changed=regs.copy();changed[1]+=1
initial=paint('01010',181,regs,[1]*167)
entry=sparse(table,initial,976)
assert entry==dense(table,initial,976)==sparse(old,initial,976)==dense(old,initial,976)
assert entry[:2]==(73,182) and all(p in entry[2] for p in (179,180,181))
entry_summary=dict(steps=976,state=73,head=182,header=181,two_cells_before_header=[1,1],required_by_local_theorem=[0,0],sparse_dense_and_both_tables_agree=True)
actual=paint('0110',180,changed,[1]*167)
run=sparse(table,initial,1556);assert run==dense(table,initial,1556)==(96,0,sorted(actual))
# The intended instruction is CI8, whose physical register is1.
intended=paint('01011',181,changed,[1]*168)
q,h,ones=96,0,initial.copy();baseline_time=None
for tick in range(1,20001):
    w,d,q=old[q,int(h in ones)]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
    if (q,h,ones)==(96,0,intended):baseline_time=tick;break
assert baseline_time is not None
assert sparse(old,initial,baseline_time)==dense(old,initial,baseline_time)==(96,0,sorted(intended))
out=dict(status='PASS_EXACT_INTEGRATION_COUNTEREXAMPLE',baseline_old_sha256=hashlib.sha256(BASE.read_bytes()).hexdigest(),candidate_old_sha256=hashlib.sha256(CAND.read_bytes()).hexdigest(),candidate_working_states=244,initial=dict(state=96,head=0,pc='01010',header_distance=181,physical_registers=regs,spare_count=167,spare_values=1),instruction=dict(op='CI',logical_register=8,physical_register=1),actual=dict(steps=1556,state=96,head=0,pc_representative='0110',pc_one_positions=[1,2],header_distance=180,physical_registers=changed,spare_count=167,spare_values=1,all_one_positions=run[2]),required=dict(baseline_steps=baseline_time,state=96,head=0,pc='01011',pc_one_positions=[1,3,4],header_distance=181,physical_registers=changed,spare_count=168,spare_values=1),independent_sparse_dense_agreement=True,scope='The local box theorem is valid. Its unchanged-caller integration is invalid: the modified table reaches a clean dispatcher frame with the wrong PC after the increment. This refutes the proposed original-source instruction contract, not every possible interpretation of this244-state table and not every smaller machine.')
out['local_macro_entry']=entry_summary
(HERE/'integration_counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='actual'},indent=2));print('actual compact',{k:v for k,v in out['actual'].items() if k!='all_one_positions'})
