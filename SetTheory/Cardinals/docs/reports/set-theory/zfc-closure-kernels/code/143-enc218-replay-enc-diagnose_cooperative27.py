"""Concrete counterexample diagnosis of four symbolic near-hits only."""
import json,time,signal
from itertools import product
import synthesize_full_returns as F
D,S=F.D,F.S;R=S.r
TOTAL=0;CAP=10_000_000;PER=1_000_000

def run(T,regs,spares,gap):
 global TOTAL
 ones=R.frame('000',regs,spares,gap);q=96;h=0;trace=[];power=1;lam=0;saved=(q,h,frozenset(ones));save_tick=0
 for tick in range(PER+1):
  if tick and R.clean_dispatch(q,h,ones):return dict(reason='first_clean_dispatch',configuration=(q,h,ones),steps=tick,trace=trace)
  if(q,int(h in ones))not in T:return dict(reason='halt_or_missing_row',configuration=(q,h,ones),steps=tick,trace=trace)
  if tick==PER:return dict(reason='per_case_cap',configuration=(q,h,ones),steps=tick)
  b=int(h in ones);w,d,z=T[q,b]
  if len(trace)<5000:trace.append([tick,F.iv[q],h,b,w,d,F.iv[z]])
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;q=z;TOTAL+=1;lam+=1
  if TOTAL>CAP:raise TimeoutError('10m aggregate steps')
  if q==saved[0]and h==saved[1]and ones==saved[2]:return dict(reason='exact_cycle',configuration=(q,h,ones),steps=tick+1,previous_tick=save_tick,period=lam,trace=trace)
  if lam==power:saved=q,h,frozenset(ones);save_tick=tick+1;power*=2;lam=0

def main():
 began=time.monotonic();signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('60 second cap')));signal.alarm(60)
 inputs=[]
 for v,other,gap,first,tail in product((1,2,3),(0,1),(0,1),(0,1),((),(0,),(1,))):
  regs=[other]*9;regs[8]=v;inputs.append((regs,[first,*tail],gap))
 for j in range(8):
  for v in(1,2):
   for gap in(0,1):
    regs=[0]*9;regs[8]=v;regs[j]=1;inputs.append((regs,[0],gap))
 inputs=inputs[:128];actions=[(0,-1,4),(0,-1,16),(0,1,54),(1,1,40)];out=[];status='COMPLETED_TARGETED_CONCRETE_DIAGNOSIS'
 try:
  for action in actions:
   T={r:a for r,a in F.T.items()if r[0]!=F.mp[302]};T[F.mp[103],1]=(0,-1,F.mp[162]);T[F.mp[113],0]=(0,-1,F.mp[27]);T[F.mp[27],0]=(action[0],action[1],F.mp[action[2]]);result=dict(action=action,cases=0,passed=0)
   for regs,spares,gap in inputs:
    result['cases']+=1;want=R.expected(['000','CD',8],regs,spares,gap);a=run(T,regs,spares,gap)
    if a['reason']=='first_clean_dispatch'and a['configuration']==want[0]:result['passed']+=1;continue
    if a['reason']=='per_case_cap':result.update(status='INCONCLUSIVE_CAP');break
    old=run(F.T,regs,spares,gap);assert old['reason']=='first_clean_dispatch'and old['configuration']==want[0]
    conf=a.pop('configuration');result.update(status='CONCRETE_INTERFACE_COUNTEREXAMPLE',registers=regs,spares=spares,gap=gap,initial_one_cells=sorted(R.frame('000',regs,spares,gap)),actual=R.describe(conf),expected=R.describe(want[0]),expected_logical=want[1],baseline_same_case_steps=old['steps'],**a);break
   else:result['status']='ALL_SELECTED_CONCRETE_CASES_PASS'
   out.append(result);print(json.dumps({k:v for k,v in result.items()if k not in('trace','actual','expected','initial_one_cells')}),flush=True)
 except TimeoutError as e:status='INCOMPLETE_AGGREGATE_CAP';out.append(dict(error=str(e)))
 finally:
  signal.alarm(0);r=dict(status=status,results=out,total_literal_steps=TOTAL,seconds=time.monotonic()-began,scope='Four near-hits only. Wrong first clean dispatch, halt, or exact repeated complete configuration is a concrete primitive-interface counterexample, not a blank-run counterexample. Caps are inconclusive.');D.dump('COOPERATIVE27_CONCRETE_DIAGNOSIS.json',r);print(status,'steps',TOTAL,'seconds',time.monotonic()-began,flush=True)
if __name__=='__main__':main()
