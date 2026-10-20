"""Finite CEGIS diagnosis for the complete 872-action cooperative family.

Wrong first-clean dispatcher endpoints, halts and exact cycles are concrete
counterexamples. A finite timeout is explicitly retained as UNKNOWN.
"""
import json,time,signal,hashlib
from collections import Counter
from itertools import product
import diagnose_cooperative27 as C
F,D,R=C.F,C.D,C.R

def main():
 began=time.monotonic();C.TOTAL=0;C.CAP=20_000_000;C.PER=10_000;fixtures=[]
 for v in(0,1):
  regs=[0]*9;regs[8]=v;fixtures.append(dict(registers=regs,spares=[0],gap=0))
 for k,(v,other,gap)in enumerate(product((0,1,2,3),(0,1),(0,1))):
  regs=[other]*9;regs[8]=v;fixtures.append(dict(registers=regs,spares=[k%2]+([0]if k%3==0 else[1]if k%3==1 else[]),gap=gap))
 expected=[];controls=[];records=[];counts=Counter();status='COMPLETE_CONCRETE_COOPERATIVE27_FILTER';current=None
 signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('60 second watchdog')));signal.alarm(60)
 try:
  for i,fx in enumerate(fixtures):
   regs,spares,gap=fx['registers'],fx['spares'],fx['gap'];want=R.expected(['000','CD',8],regs,spares,gap);a=C.run(F.T,regs,spares,gap);assert a['reason']=='first_clean_dispatch'and a['configuration']==want[0]
   expected.append(want);controls.append(dict(fixture=i,steps=a['steps'],actual=R.describe(a['configuration'])));fx['initial_one_cells']=sorted(R.frame('000',regs,spares,gap));fx['expected']=R.describe(want[0]);fx['expected_logical']=want[1]
  Q=sorted({q for q,b in F.N}-{302})
  for w,d,z in product((0,1),(-1,1),Q):
   current=[w,d,z];T={r:a for r,a in F.T.items()if r[0]!=F.mp[302]};T[F.mp[103],1]=(0,-1,F.mp[162]);T[F.mp[113],0]=(0,-1,F.mp[27]);T[F.mp[27],0]=(w,d,F.mp[z]);rec=dict(action=current,passed_fixtures=[],capped_fixtures=[]);counts['actions']+=1
   for i,fx in enumerate(fixtures):
    a=C.run(T,fx['registers'],fx['spares'],fx['gap']);counts['case_runs']+=1
    if a['reason']=='first_clean_dispatch'and a['configuration']==expected[i][0]:rec['passed_fixtures'].append(i);continue
    if a['reason']=='per_case_cap':rec['capped_fixtures'].append(i);continue
    rec.update(status='CONCRETE_REJECTION',failed_fixture=i,reason=a['reason'],steps=a['steps'],actual=R.describe(a['configuration']));counts[a['reason']]+=1
    if a['reason']=='exact_cycle':rec.update(previous_tick=a['previous_tick'],period=a['period'])
    break
   else:rec['status']='UNKNOWN_CAPPED'if rec['capped_fixtures']else'ALL_18_FINITE_FIXTURES_PASS'
   counts[rec['status']]+=1;records.append(rec)
   if counts['actions']%200==0:print('ACTIONS',counts['actions'],'steps',C.TOTAL,'results',dict(counts),flush=True)
 except TimeoutError as e:status='INCOMPLETE_AGGREGATE_CAP';current=dict(action=current,error=str(e))
 finally:
  signal.alarm(0);pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in[D.BASE/'k219.native.tm',D.D/'concrete_filter_cooperative27.py',D.D/'diagnose_cooperative27.py']};r=dict(status=status,counts=dict(counts),actions=records,fixtures=fixtures,baseline_controls=controls,steps=C.TOTAL,seconds=time.monotonic()-began,current=current,input_pins=pins,per_case_cap=C.PER,total_step_cap=C.CAP,scope='Only the fixed three-row family:103/1=0L162,113/0=0L27,delete302,and enumerate872 actions for27/0. A concrete rejection disproves this established primitive interface, not every possible equiconsistent interpretation. Caps are unknown. Finite survivors require universal symbolic proof and full-machine validation.');D.dump('COOPERATIVE27_ALL_ACTIONS_CONCRETE.json',r);print(json.dumps({k:v for k,v in r.items()if k not in('actions','fixtures','baseline_controls','input_pins')}),flush=True)
if __name__=='__main__':main()
