#!/usr/bin/env python3
"""Lexical source-header audit, with in-memory patch controls; no Lean."""
from pathlib import Path
from collections import deque
import hashlib,json,re
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-slim-overlay'
I=A/'inventory.json';assert hashlib.sha256(I.read_bytes()).hexdigest()=='b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e';j=json.loads(I.read_bytes())
rows={r['module']:r for r in j['drafts_topological']};edges={m:r['bare_imports']+r['qualified_imports'] for m,r in rows.items()}
for m,r in j['project_sources'].items():
 p=D/r['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];assert m not in edges;edges[m]=r['imports']
target='Mathlib.Tactic.LinearCombination';users={}
for m,r in rows.items():
 p=A/r['path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['overlay_sha256'];lines=[i for i,x in enumerate(b.decode().splitlines(),1) if re.search(r'\blinear_combination\b',x)]
 if lines:users[m]=lines
expected={'AuxNorm','AuxNorm85','AuxNorm87','OwnZeroGuardStrict74','P88FourSquareModel','P88PairModel','PairEvalRingBridge','ParentTo88Guard'}
assert set(users)==expected

def reachable(start,extra=None):
 todo=deque([(start,)]);seen={start};path=None;leaves=set()
 while todo:
  cur=todo.popleft();node=cur[-1]
  if node==target and path is None:path=list(cur)
  if node not in edges:leaves.add(node);continue
  nxt=edges[node]+([target] if node==extra else [])
  for x in nxt:
   if x not in seen:seen.add(x);todo.append(cur+(x,))
 return {'shortest_observed_path':path,'unexpanded_leaf_count':len(leaves),'unexpanded_leaves':sorted(leaves)}
results={m:{'lines':users[m],**reachable(m)} for m in sorted(users)}
unresolved=sorted(m for m,v in results.items() if v['shortest_observed_path'] is None)
assert unresolved==['OwnZeroGuardStrict74','PairEvalRingBridge']
patches={'OwnZeroGuardStrict74':D/'research/ordinary14-74-guard-linear-combination-patch/OwnZeroGuardStrict74.lean.src','PairEvalRingBridge':D/'research/ordinary14-pair-eval-linear-combination-patch/PairEvalRingBridge.lean.src'}
control={}
for m,p in patches.items():
 old=(A/rows[m]['path']).read_bytes();new=p.read_bytes();prefix=b'import Mathlib.Tactic.LinearCombination\n';assert new==prefix+old
 observed=reachable(m,extra=m);assert observed['shortest_observed_path']==[m,target]
 control[m]={'patch_sha256':hashlib.sha256(new).hexdigest(),'in_memory_path':observed['shortest_observed_path']}
print(json.dumps({'scope':'lexical recorded source headers, not Lean import resolution; external package/Foundation leaves unexpanded','overlay_inventory_sha256':hashlib.sha256(I.read_bytes()).hexdigest(),'target':target,'tactic_users':results,'no_recorded_path_users':unresolved,'preventive_patch_controls':control},sort_keys=True,indent=2))
