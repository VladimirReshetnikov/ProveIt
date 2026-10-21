import sys,os
if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):raise SystemExit("Disable Python optimization")
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[1];D=Path(__file__).resolve().parent
p=R/'machine/source.sites.json'
s=json.loads(p.read_text());N=len(s);start={};end={}
for i,(pc,op,k)in enumerate(s):
 for z in range(len(pc)+1):start.setdefault(pc[:z],i);end[pc[:z]]=i+1
G=[]
for i,(pc,op,k)in enumerate(s):
 bs=[end[pc[:z]]%N for z,b in enumerate(pc)if b=='0'];cs=[start[pc[:z]]for z,b in enumerate(pc)if b=='1'];stk=bs if op in ('CD','CB')else cs;depth=1 if op=='CD'else k if op in('CB','CC')else 1;target=stk[-depth]if len(stk)>=depth else 0
 G.append((op,k, []if op=='CH'else[target]if op in('CB','CC')else[target,(i+1)%N]if op=='CD'else[(i+1)%N]))
assert s[4697]==['100111','CC',3] and G[4697][2]==[23]
parent_path=R/'inputs/composite_transfer.sites.json'
parent=json.loads(parent_path.read_text())
old_ax=[(pc[len('1101001'):],op,k) for pc,op,k in parent if pc.startswith('1101001')]
new_ax=[(pc[len('1001001'):],op,k) for pc,op,k in s if pc.startswith('1001001')]
assert old_ax==new_ax and len(old_ax)==4565
assert G[4589][2]==[4696]
traces=[]
for top in [0,1,2,10,100]:
 v=[1,top,3,0,0,0,0,0,0];j=4696;trace=[]
 for step in range(1000):
  trace.append([j,v.copy()]);op,k,e=G[j]
  if op=='CH':break
  if op=='CI':v[k]+=1;j=e[0]
  elif op=='CD':b=v[k]>0;v[k]-=int(b);j=e[int(b)]
  else:j=e[0]
 else:raise AssertionError('timeout')
 assert j==4718
 traces.append(dict(initial_top=top,steps=step,halt_ordinal=j,trace=trace))
receipt=dict(status='CONFIRMED_RETURN_TARGET_ERROR',source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),path='100111',operation='CC3',actual_target_ordinal=23,claimed_target_ordinal=0,AX_subtree_identical=True,AX_subtree_leaves=len(old_ax),AX_exit_target=4696,counterexamples=traces)
assert receipt==json.loads((R/'evidence/RETURN_TARGET_COUNTEREXAMPLE.json').read_text());print({k:v for k,v in receipt.items()if k!='counterexamples'});print([(x['initial_top'],x['steps'])for x in traces]);print(traces[0]['trace'])
