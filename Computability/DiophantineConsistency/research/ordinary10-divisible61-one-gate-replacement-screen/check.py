#!/usr/bin/env python3
"""Bounded literal-DAG exact-target replacement screen via modular controls."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
g=json.loads((root/'research/ordinary10-two-norm-divisible61/candidate.json').read_text())
rows=g['source']; leaves=g['witnesses']+g['fixed_numerals']; assert len(rows)==61 and len(leaves)==14
p=1000000007;trials=4
def val(name,j):
 key=('codex61-replacement-v1:'+str(j)+':'+name).encode()
 return 1+int.from_bytes(hashlib.sha256(key).digest(),'big')%(p-1)
e={n:tuple(val(n,j) for j in range(trials)) for n in leaves}
for k in range(-1,5):e[k]=(k%p,)*trials
def calc(op,x,y):
 if op=='+':return tuple((a+b)%p for a,b in zip(x,y))
 if op=='-':return tuple((a-b)%p for a,b in zip(x,y))
 return tuple((a*b)%p for a,b in zip(x,y))
for name,op,a,b in rows:e[name]=calc(op,e[a],e[b])
parents={n:(a,b) for n,op,a,b in rows}
assert len(parents)==61
stack=[g['output']];baseline=set()
while stack:
 x=stack.pop()
 if not isinstance(x,str) or x not in parents or x in baseline:continue
 baseline.add(x);stack.extend(parents[x])
assert len(baseline)==61
def live(target,args,is_alias):
 seen=set();todo=[g['output']]
 while todo:
  n=todo.pop()
  if not isinstance(n,str) or n not in parents or n in seen:continue
  seen.add(n)
  todo.extend(args if n==target else parents[n])
 return len(seen)-(1 if target in seen and is_alias else 0)
alias_count=binary_count=matches=saving_matches=0;sample_matches=[0]*trials
for index,(target,oldop,olda,oldb) in enumerate(rows):
 available=leaves+list(range(-1,5))+[x[0] for x in rows[:index]]
 goal=e[target]
 for v in available:
  alias_count+=1
  if e[v]!=goal:continue
  matches+=1
  if live(target,(v,),True)<61:saving_matches+=1
 for i,a in enumerate(available):
  for j,b in enumerate(available):
   for op in ('+','-','*'):
    if op in ('+','*') and j<i:continue
    binary_count+=1
    value=calc(op,e[a],e[b])
    if value!=goal:continue
    matches+=1
    if live(target,(a,b),False)<61:saving_matches+=1
assert saving_matches==0
print(json.dumps({'literal_live_rows':len(baseline),'targets':len(rows),'trials':trials,
 'prime':p,'seed_rule':'sha256 codex61-replacement-v1:trial:input',
 'candidate_literals':list(range(-1,5)),'candidate_aliases_tested':alias_count,
 'candidate_binary_expressions_tested':binary_count,
 'all_trial_signature_matches':matches,'gate_saving_signature_matches':saving_matches,
 'every_excluded_candidate_has_modular_counterexample':True,
 'global_gate_lower_bound_or_zero_set_claim':False,'lean_executed':False},indent=2,sort_keys=True))
