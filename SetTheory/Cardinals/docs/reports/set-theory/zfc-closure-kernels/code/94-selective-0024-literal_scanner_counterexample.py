#!/usr/bin/env python3
"""Exact complete configurations showing the wrong first clean frame.

This disproves agreement of the first complete source-instruction boundary;
it does not assert different eventual halting from this frame or blank start.
"""
from pathlib import Path
import json
import os
BASE=Path(os.environ.get('ZFC245_REFERENCE', str(Path(__file__).resolve().parent.parent/'packages/zfc245-proof-20261018'))).resolve()
T={}
for line in (BASE/'certificate/machine_old.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
M={k:v for k,v in T.items() if k[0]!=58};M[41,0]=(0,-1,84)
pc='11101001001000000';D=64
initial={-1,D}|{i for i,b in enumerate(pc)if b=='1'}
pos=D+1
for value in [0]*9+[1]:
    pos+=1;initial.update(range(pos,pos+value+1));pos+=value+1
successor=pc[:-1];successor=format(int(successor,2)+1,f'0{len(successor)}b')
target=(initial-set(range(len(pc))))|{i for i,b in enumerate(successor) if b=='1'}

def run(table,fuel=10000):
    q,h,t=96,0,set(initial);seen={};dispatches=[]
    for tick in range(fuel+1):
        c=(q,h,tuple(sorted(t)))
        clean=(q==96 and h==0 and
               {x for x in t if x<0}=={-1} and
               not any(51<=x<D for x in t) and
               {x for x in t if x>=D}=={x for x in initial if x>=D})
        if tick and clean:return {'status':'EXPECTED_FIRST_CLEAN_FRAME' if t==target else 'DIFFERENT_FIRST_CLEAN_FRAME','steps':tick,'state':q,'head':h,'ones':sorted(t),'dispatches':dispatches}
        if c in seen:return {'status':'EXACT_CYCLE','steps':tick,'cycle_start':seen[c],'period':tick-seen[c],'state':q,'head':h,'ones':sorted(t),'dispatches':dispatches}
        seen[c]=tick
        if tick and q==96 and len(dispatches)<20:dispatches.append({'steps':tick,'head':h,'ones':sorted(t)})
        if (q,int(h in t))not in table:return {'status':'HALT','steps':tick,'state':q,'head':h,'ones':sorted(t),'dispatches':dispatches}
        if tick==fuel:break
        w,d,q=table[q,int(h in t)]
        if w:t.add(h)
        else:t.discard(h)
        h+=d
    return {'status':'BOUND','fuel':fuel,'state':q,'head':h,'ones':sorted(t),'dispatches':dispatches}
def dense_at(table,steps):
    cells=bytearray(2*steps+2*D+20);origin=steps+D+2
    for x in initial:cells[origin+x]=1
    q,h=96,origin
    for _ in range(steps):
        w,d,q=table[q,cells[h]];cells[h]=w;h+=d
    return q,h-origin,[i-origin for i,b in enumerate(cells) if b]

baseline,mutant=run(T),run(M)
assert baseline['status']=='EXPECTED_FIRST_CLEAN_FRAME' and baseline['steps']==574
assert mutant['status']=='DIFFERENT_FIRST_CLEAN_FRAME' and mutant['steps']==650
assert set(baseline['ones'])==initial|{15} and set(mutant['ones'])==initial|{13}
for table,result in [(T,baseline),(M,mutant)]:
    assert dense_at(table,result['steps'])==(result['state'],result['head'],result['ones'])
result={'scope':'Exact first clean-frame disagreement only; no blank reachability or halting inequivalence claim.','path':pc,'opcode':'CD','physical_register':2,'branch':'zero','header_distance':D,'physical_registers':[0]*9,'spares':[1],'initial':{'state':96,'head':0,'ones':sorted(initial)},'expected':{'state':96,'head':0,'pointer':successor,'ones':sorted(target)},'baseline':baseline,'mutant':mutant,'sparse_dense_exact_agreement':True,'compact_difference':{'common_one_cells':sorted(initial),'baseline_adds':[15],'mutant_adds':[13]}}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('baseline','mutant','initial','expected')},indent=2))
