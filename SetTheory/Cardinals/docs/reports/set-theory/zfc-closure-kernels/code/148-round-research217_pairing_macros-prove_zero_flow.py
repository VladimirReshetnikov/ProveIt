#!/usr/bin/env python3
"""Owned coarse inductive scratch proof independent of either pairing codec."""
from pathlib import Path
import collections,hashlib,json,sys,time
D=Path(__file__).resolve().parent;ROOT=D.parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
r=json.loads((D/'MACRO_INVENTORY.json').read_text());old={freeze(x['old_ast']):('M_'+x['name'],None)for x in r['inventory']};new={freeze(x['new_ast']):('M_'+x['name'],None)for x in r['inventory']}
def collapse(t,macros):
 if t in macros:return macros[t]
 if A.P.leaf(t):return t
 return(collapse(t[0],macros),collapse(t[1],macros))
op=ROOT/'latest218_baseline/candidate-k218/sites218.json';np=D/'three_macros.sites.json'
a=collapse(A.P.tree(json.loads(op.read_text())),old);b=collapse(A.P.tree(json.loads(np.read_text())),new);assert a==b
cfg=A.continuation_cfg(a);sites=A.flatten(a);N=len(cfg);facts=[None]*N
seed=[3,0,0,0,3,0,0,0,0];facts[0]=[2 if x else 1 for x in seed];todo=collections.deque([0]);queued={0};updates=0;beg=time.monotonic()
def outputs(i,st):
 op,arg,targets=cfg[i]
 if op.startswith('M_'):
  out=st.copy()
  if op=='M_pair':out[1]=out[6]=1;out[7]=3
  else:out[8 if op=='M_unpair8'else 2]=1;out[6]=out[7]=3
  return[(targets[0],out)]
 if op=='CH':return[]
 if op=='CD':
  out=[]
  if st[arg]&1:
   z=st.copy();z[arg]=1;out.append((targets[0],z))
  if st[arg]&2:
   z=st.copy();z[arg]=3;out.append((targets[1],z))
  return out
 out=st.copy()
 if op=='CI':out[arg]=2
 return[(targets[0],out)]
while todo:
 i=todo.popleft();queued.remove(i)
 for j,st in outputs(i,facts[i]):
  oldst=facts[j];merged=st if oldst is None else[x|y for x,y in zip(oldst,st)]
  if merged!=oldst:
   facts[j]=merged;updates+=1
   if j not in queued:todo.append(j);queued.add(j)
assert all((2 if v else 1)&~facts[0][i]==0 for i,v in enumerate(seed))
edges=0
for i,st in enumerate(facts):
 if st is not None:
  for j,out in outputs(i,st):assert facts[j]is not None and all(x&~y==0 for x,y in zip(out,facts[j]));edges+=1
calls=[]
for i,(op,arg,targets)in enumerate(cfg):
 if op.startswith('M_'):
  st=facts[i]
  assert st is not None and st[7]==1 and(op=='M_pair'or st[6]==1),(i,op,st)
  calls.append(dict(index=i,macro=op,registers=st))
result=dict(status='CODEC_INDEPENDENT_SCRATCH_ENTRY_INVARIANT_PASS',old_source_sha256=H(ROOT/'latest218_baseline/candidate-k218/sites218.json'),new_source_sha256=H(np),virtual_primitives=N,virtual_macro_calls=len(calls),enabled_edges=edges,updates=updates,seconds=time.monotonic()-beg,domain={'1':'exactly zero','2':'positive natural','3':'arbitrary natural'},calls=calls,facts=facts,scope='The two sources collapse to the identical control tree when these exact closed macros are treated as normally returning calls. All numeric macro outputs are conservatively arbitrary; only cleared registers are fixed. The listed invariant is seed-containing and edge-inductive, and every call satisfies its scratch precondition. This proves scratch guards for the changed codec without Cantor-specific values or Con(ZFC). It does not prove the new codec parser, scheduler fairness or Turing-machine implementation.')
(D/'ZERO_FLOW_PROOF.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k not in('facts','calls')})
