#!/usr/bin/env python3
"""Bounded CEGIS discovery of a five-state unary arithmetic core.

This is a search, not a universal proof. The fixed surrounding four states
are actual Prefix246 rows. Every candidate must subsequently be audited.
"""
from pathlib import Path
import sys,json,time,itertools,argparse
sys.path.insert(0,str(Path(__file__).resolve().parent/'deps'))
from z3 import *

OLD=[73,83,95,109,75,48,63,112,131]
IDX={q:i for i,q in enumerate(OLD)}
FIXED={
  (5,0):(0,False,10),(5,1):(1,False,6),
  (6,0):(0,False,5),(6,1):(1,False,6),
  (7,0):(1,False,8),(7,1):(1,False,7),
  (8,0):(0,False,5),(8,1):(0,False,7),
}
BASE={
 (0,0):(0,True,1),(0,1):(1,True,0),
 (1,0):(1,True,2),(1,1):(1,True,0),
 (2,0):(1,True,3),(2,1):(1,True,2),
 (3,0):(0,True,4),(3,1):(0,True,2),
 (4,0):(1,True,11),(4,1):(1,False,6),
}
def word(vs):return [b for v in vs for b in [0]+[1]*(v+1)]
def support(vs):return sum(b<<(16+i) for i,b in enumerate(word(vs)))
def case(prefix,x,suffix,mode):
 vs=list(prefix)+[x]+list(suffix);r=len(prefix)
 if mode=='zero':vs[r]=0
 if mode=='positive' and vs[r]==0:vs[r]=1
 mask=support(vs);mask &= ~(1<<(17+sum(v+2 for v in vs[:r])))
 # Immutable arbitrary-looking left context; head never crosses it before exit.
 left=(1<<14)|(1<<12)|(1<<9)|(1<<8);mask|=left
 if mode=='increment':
  vs[r]+=1;targets=[support(vs+s)|left for s in ([],[0],[1],[2])];q,h=5,15;start=0
 elif mode=='positive':
  vs[r]-=1;targets=[(support(vs)<<1)|(1<<16)|left];q,h=5,16;start=2
 else:targets=[support(vs)|left];q,h=7,15;start=2
 return dict(prefix=list(prefix),x=x,suffix=list(suffix),mode=mode,initial=mask,targets=targets,
  start=start,target_q=q,target_h=h,bound=2*len(word(list(prefix)+[x]+list(suffix)))+18)
def validate(tab,c):
 tape=c['initial'];q=c['start'];h=16
 for t in range(c['bound']*3):
  if q==c['target_q'] and h==c['target_h'] and tape in c['targets']:return True,t
  if h<16 or h>=60 or q>=9:return False,t
  b=(tape>>h)&1;w,d,q=tab[q,b]
  tape=(tape|(1<<h)) if w else (tape&~(1<<h));h+=1 if d else -1
 return False,c['bound']*3

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--edits',type=int,default=5);ap.add_argument('--timeout',type=int,default=45000);args=ap.parse_args()
 s=Solver();s.set(timeout=args.timeout)
 W={};D={};Q={};cost=[]
 for q in range(9):
  for b in range(2):
   if q<5:
    W[q,b]=Bool(f'w_{q}_{b}');D[q,b]=Bool(f'd_{q}_{b}');Q[q,b]=BitVec(f'q_{q}_{b}',4)
    s.add(ULE(Q[q,b],8));ow,od,oq=BASE[q,b]
    cost.append(If(And(W[q,b]==bool(ow),D[q,b]==od,Q[q,b]==oq),0,1))
   else:
    w,d,t=FIXED[q,b];W[q,b]=BoolVal(bool(w));D[q,b]=BoolVal(d);Q[q,b]=BitVecVal(t,4)
 s.add(Sum(cost)<=args.edits)
 for qb in [(0,1),(2,1),(3,1)]:
  ow,od,oq=BASE[qb];s.add(W[qb]==bool(ow),D[qb]==od,Q[qb]==oq)
 def lookup(data,q,b):
  out=data[8,1]
  for i in reversed(range(9)):
   for j in reversed(range(2)):
    out=If(And(q==i,b==bool(j)),data[i,j],out)
  return out
 allcases=[case(p,x,s,m) for p,x,s,m in itertools.product([[],[0],[1],[0,1]],[0,1,2],[[0],[1],[0,1]],['zero','positive','increment'])]
 chosen=[]
 def add_case(c):
  k=len(chosen);chosen.append(c)
  q=BitVec(f's{k}_0',4);h=BitVec(f'h{k}_0',6);tape=BitVec(f't{k}_0',64);done=Bool(f'done{k}_0')
  stop=BitVec(f'stop{k}',6);s.add(ULE(stop,c['bound']),UGE(stop,1))
  s.add(q==c['start'],h==16,tape==c['initial'],Not(done))
  for i in range(c['bound']):
   goal=And(q==c['target_q'],h==c['target_h'],Or([tape==x for x in c['targets']]))
   b=(LShR(tape,ZeroExt(58,h))&1)==1;w=lookup(W,q,b);d=lookup(D,q,b);nq=lookup(Q,q,b)
   q1=BitVec(f's{k}_{i+1}',4);h1=BitVec(f'h{k}_{i+1}',6);t1=BitVec(f't{k}_{i+1}',64);done1=Bool(f'done{k}_{i+1}')
   frozen=ULE(stop,i);s.add(done1==frozen)
   s.add(Or(frozen,And(ULE(q,8),UGE(h,16),ULT(h,60))))
   s.add(q1==If(frozen,q,nq),h1==If(frozen,h,If(d,h+1,h-1)))
   shift=BitVecVal(1,64)<<ZeroExt(58,h)
   s.add(t1==If(frozen,tape,If(w,tape|shift,tape&~shift)))
   q,h,tape,done=q1,h1,t1,done1
  goal=And(q==c['target_q'],h==c['target_h'],Or([tape==x for x in c['targets']]))
  s.add(goal)
  print('ADD',k,{a:c[a] for a in ['prefix','x','suffix','mode','bound']},flush=True)
 for mode in ['zero','positive','increment']:add_case(case([],1,[0],mode))
 began=time.monotonic();iterations=[]
 for it in range(50):
  ans=s.check();print('SOLVE',it,ans,'seconds',time.monotonic()-began,flush=True)
  if ans!=sat:
   result=dict(status=str(ans),edits=args.edits,cases=len(chosen),iterations=iterations,reason=s.reason_unknown() if ans==unknown else None,seconds=time.monotonic()-began)
   break
  m=s.model();tab=dict(FIXED)
  for q in range(5):
   for b in range(2):tab[q,b]=int(is_true(m.eval(W[q,b]))),is_true(m.eval(D[q,b])),m.eval(Q[q,b]).as_long()
  failures=[c for c in allcases if not validate(tab,c)[0]]
  changes=[(OLD[q],b,[w,'R' if d else 'L',OLD[t]]) for (q,b),(w,d,t) in tab.items() if q<5 and (w,d,t)!=BASE[q,b]]
  print('CANDIDATE',changes,'failures',len(failures),flush=True)
  iterations.append(dict(changes=changes,failures=len(failures)))
  if not failures:
   result=dict(status='finite_candidate',table={f'{OLD[q]} {b}':[w,'R' if d else 'L',OLD[t] if t<9 else -1] for (q,b),(w,d,t) in tab.items()},edits=args.edits,iterations=iterations,seconds=time.monotonic()-began)
   break
  for c in failures[:3]:add_case(c)
 else:result=dict(status='iteration_limit',iterations=iterations)
 p=Path(__file__).with_name(f'synthesis_structured_edits{args.edits}.json');p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
