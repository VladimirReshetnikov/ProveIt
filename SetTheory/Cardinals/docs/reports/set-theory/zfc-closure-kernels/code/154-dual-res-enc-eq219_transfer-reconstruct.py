#!/usr/bin/env python3
"""Reconstruct finite equality hits with a potentially changed parameter D.

The first private-code gate is deliberately excluded from source replacements.
This script does not supply a runtime or logical certificate for a new table.
"""
import importlib.util,itertools,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import inverse_mp as q
import recompile219 as compiler
s,b=q.s,q.b
BASE=q.W/'K219_Construction_2026-10-20'
spec=importlib.util.spec_from_file_location('eqcheck',BASE/'research/encoding/verify_clean_eq.py')
check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
def tup(n):return tuple(tup(v)if isinstance(v,list)else v for v in n)
atoms=[tup(a)for a in json.loads((HERE/'atoms.json').read_text())]
g=dict(enumerate(atoms));hits=[]
for line in (HERE/'nodes6.txt').read_text().splitlines():
 parts=line.split()
 if parts[0]=='H':
  a,bb,c=map(int,parts[1:]);hits.append((g[a],g[bb]))
 else:
  i,a,bb,c=map(int,parts);g[i]=(g[a],g[bb])
table=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
old=s.tree(json.loads((BASE/'machine/sites219.json').read_text()))
paths=['11101001001110111110','1110100101100','111110']
def run(tree,a,bb):
 graph=check.compile_cfg(((tree,('CI',0)),('CH',None)))
 initial=[17,19,23,29,31,a,bb,37,41];regs=list(initial);pc=0
 for step in range(100*(a+bb+1)+1000):
  op,arg,targets=graph[pc]
  if op=='CH':
   target=list(initial);target[0]+=a==bb;target[5]=target[6]=0
   target[4]=regs[4]
   assert regs==target,(a,bb,regs,target)
   assert a!=bb or regs[4]==initial[4],('success_changes_D',a,bb,regs)
   return regs[4]-initial[4]
  if op=='CI':regs[arg]+=1;pc=targets[0]
  elif op=='CD':
   positive=regs[arg]>0
   if positive:regs[arg]-=1
   pc=targets[int(positive)]
  else:pc=targets[0]
 raise ValueError(('timeout',a,bb,pc,regs))
results=[]
for idx,tree in enumerate(hits):
 row={'hit':idx,'tree':tree,'source_claim':'finite diagnostic only'}
 try:
  ds=[run(tree,a,bb)for a in range(25)for bb in range(25)]
  ds.extend(run(tree,a,bb)for a,bb in [(0,1000),(1000,0),(1000,1000),(999,1000),(1000,999)])
  row['finite_cases']=len(ds);row['maximum_D_increment']=max(ds)
 except Exception as exc:row['finite_error']=repr(exc);results.append(row);print(json.dumps(row),flush=True);continue
 layouts=[]
 for mask in range(1,8):
  new=old
  for j,p in enumerate(paths):
   if mask>>j&1:new=s.replace(new,p,tree)
  metric=s.metrics(new);rec={'replacement_mask':mask,'metrics':metric}
  if metric['dag_nodes']<=207:
   try:
    U,meta=compiler.compile_tree(table,old,new,extend_direct=True);rec['compiler']=meta
    if meta['working_states']<=219:
     d=HERE/f'hit{idx}_mask{mask}';d.mkdir(exist_ok=True)
     (d/'sites.json').write_bytes(s.compact(s.sites(new)));(d/'candidate.tm').write_bytes(b.table_bytes(U))
     (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
   except Exception as exc:rec['compile_error']=repr(exc)
  layouts.append(rec)
 row['layouts']=layouts;results.append(row)
 print(json.dumps({k:v for k,v in row.items()if k!='tree'}),flush=True)
(HERE/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
