#!/usr/bin/env python3
"""Independent dictionary-tape replay of a small bounded54/0 obstruction."""
from pathlib import Path
import argparse,importlib.util,json,hashlib
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
sp=importlib.util.spec_from_file_location('inv',HERE/'invariant.py');inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
T,start=inv.read(a.table);R=5;CAP=96;dead=40;root=(54,0)
assert T[40,0]==(0,-1,4) and T[40,1]==(1,-1,54)
assert T[54,0]==(0,-1,40) and T[54,1]==(1,-1,54)
cut={k for k,v in T.items() if k[0]!=dead and v[2]==dead}
assert cut=={(27,1),(54,0),(198,0)}
I=inv.analyze(T,start,R,False)
contexts=[m for m in I['masks'][54] if not(m>>R&1)]
states=sorted({q for q,b in T});actions=[(w,d,q) for q in states+[254] if q!=dead for w in(0,1) for d in(-1,1)]
def initial(m):return {j-R:(m>>j)&1 for j in range(2*R+1)}
def conf(q,h,tape):return(q,h,tuple(sorted(tape.items())))
def old_goals(m):
 q=54;h=0;tape=initial(m);goals=set();trace=[]
 for n in range(CAP):
  if h not in tape or q==254:break
  row=(q,tape[h])
  if n and row in cut and row!=root:break
  w,d,q=T[row];tape[h]=w;h+=d;trace.append((q,h))
  if q!=dead:goals.add(conf(q,h,tape))
 return goals,trace
def passes(m,patch):
 goals,_=old_goals(m);q=54;h=0;tape=initial(m)
 for n in range(CAP):
  if h not in tape or q in(254,dead):return False
  row=q,tape[h]
  if n and row in cut and row!=root:return False
  w,d,q=patch if row==root else T[row];tape[h]=w;h+=d
  if q==dead:return False
  if conf(q,h,tape) in goals:return True
 return False
survivors=actions[:];witnesses=[]
for m in contexts:
 before=len(survivors);survivors=[x for x in survivors if passes(m,x)]
 if len(survivors)<before:
  goals,trace=old_goals(m)
  witnesses.append({'mask':m,'window_left_to_right':''.join(str(initial(m)[j]) for j in range(-R,R+1)),'head_index':R,'before':before,'after':len(survivors),'old_control_head_trace':trace,'old_goal_count':len(goals),'remaining_actions':survivors})
 if not survivors:break
assert not survivors
# Independent full replay of all860 choices against just the retained witnesses.
assert all(any(not passes(w['mask'],x) for w in witnesses) for x in actions)
receipt={'status':'BOUNDED_OBSTRUCTION_REPLAY_PASS','table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'radius':R,'cap':CAP,'original_control':54,'original_symbol':0,'deleted':dead,'action_count':len(actions),'witness_count':len(witnesses),'witnesses':witnesses,'scope':'No existing-state-or-halt replacement action passes these local joins with no state40 and no other incoming40 row in the macro interior. The windows are abstract invariant elements, not claimed blank-reachable. This is no semantic impossibility or state-count lower bound.'}
a.out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='witnesses'}))
