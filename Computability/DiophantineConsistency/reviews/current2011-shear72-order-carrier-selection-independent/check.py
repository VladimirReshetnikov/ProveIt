#!/usr/bin/env python3
"""Exact source alternative, selected frontier and witnessed source import paths."""
import copy,hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha((here/'pins.json').read_bytes())=='6eb06b62fb74f26c4ba5f3834c5ae50c2bff1958c2b40dca464f81db6b9f1e83','review pins')
pins=json.loads((here/'pins.json').read_bytes())
for p,h in pins.items():need(sha((root/p).read_bytes())==h,'pin '+p)
def read(p):return (root/p).read_text()
old=read('research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src');new=read('research/current2011-shear72-order-carrier-selection/ShearOrder.lean.src')
a='import DiophantineConsistency.ModelCarrierSpheres\n';b='import DiophantineConsistency.Carrier65\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.ByContra\n'
need(old.count(a)==1 and old.replace(a,b,1)==new,'exact import-only delta')
prev=json.loads(read('research/current2011-shear72-private-extraction-source-selection/selection.json'));sel=json.loads(read('research/current2011-shear72-order-carrier-selection/selection.json'))
expected=copy.deepcopy(prev);expected['drafts']['ShearOrder']=sel['drafts']['ShearOrder'];expected['frontier'].pop('DiophantineConsistency.ModelCarrierSpheres')
for k in ('DiophantineConsistency.Carrier65','Mathlib.Tactic.Linarith','Mathlib.Tactic.ByContra'):expected['frontier'][k]=sel['frontier'][k]
need(expected==sel and len(sel['drafts'])==15 and len(sel['frontier'])==13,'exact selected-frontier change')
need(sel['drafts']['ShearOrder']['imports']==['DiophantineConsistency.Carrier65','Mathlib.Tactic.Linarith','Mathlib.Tactic.ByContra'],'import header')
# Check full selected direct edges, independent Kahn traversal and reachability.
headers={};used=set()
for name,v in sel['drafts'].items():
 data=(root/v['path']).read_bytes();imports=[x.split()[1] for x in data.decode().splitlines() if x.startswith('import ')]
 need(sha(data)==v['sha256'] and imports==v['imports'],'selected '+name);headers[name]=imports
 for x in imports:
  if x not in sel['drafts']:need(x in sel['frontier'],'unknown frontier '+x);used.add(x)
need(used==set(sel['frontier']),'frontier cut')
for n,v in sel['frontier'].items():
 if v['kind']!='external-unexamined':need(sha((root/v['path']).read_bytes())==v['sha256'],'frontier '+n)
remaining=set(headers);order=[]
while remaining:
 ready=sorted(n for n in remaining if all(x not in remaining for x in headers[n] if x in headers))
 need(ready,'cycle');order+=ready;remaining.difference_update(ready)
q=['DiophantineConsistency.Shear72JointIPRA'];seen=set()
while q:
 n=q.pop()
 if n in seen:continue
 seen.add(n);q.extend(x for x in headers[n] if x in headers)
need(seen==set(headers),'unreachable')
# Witness exact source-level paths; public imports checked in modern module files.
paths=[
 [('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith.lean','public import Mathlib.Tactic.NormNum'),('../../.lake/packages/mathlib/Mathlib/Tactic/NormNum.lean','public import Mathlib.Tactic.NormNum.Basic'),('../../.lake/packages/mathlib/Mathlib/Tactic/NormNum/Basic.lean','public import Mathlib.Algebra.Ring.Defs')],
 [('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith.lean','public import Mathlib.Tactic.Linarith.Frontend'),('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith/Frontend.lean','public import Mathlib.Tactic.Linarith.Preprocessing'),('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith/Preprocessing.lean','public import Mathlib.Tactic.CancelDenoms.Core'),('../../.lake/packages/mathlib/Mathlib/Tactic/CancelDenoms/Core.lean','public import Mathlib.Algebra.Order.Ring.Defs')],
 [('Lean/DiophantineConsistency/Carrier65.lean','import DiophantineConsistency.ShortSystem'),('Lean/DiophantineConsistency/ShortSystem.lean','import DiophantineConsistency.ConsecutivePell'),('Lean/DiophantineConsistency/ConsecutivePell.lean','import Mathlib.Data.Int.Basic'),('../../.lake/packages/mathlib/Mathlib/Data/Int/Basic.lean','public import Mathlib.Data.Nat.Basic'),('../../.lake/packages/mathlib/Mathlib/Data/Nat/Basic.lean','public import Mathlib.Order.Defs.LinearOrder')],
 [('../../.lake/packages/mathlib/Mathlib/Tactic/ByContra.lean','public import Batteries.Tactic.Init')]]
for path in paths:
 for file,line in path:need(line in read(file).splitlines(),'import path '+line)
for file,token in [('Lean/DiophantineConsistency/Carrier65.lean','let V := f ^ 2 * (c * T - rank) - c'),('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith/Frontend.lean','syntax (name := nlinarith)'),('../../.lake/packages/batteries/Batteries/Tactic/Init.lean','syntax (name := byContra)'),('../../.lake/packages/mathlib/Mathlib/Algebra/Ring/Defs.lean','class CommRing'),('../../.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean','class IsStrictOrderedRing'),('../../.lake/packages/mathlib/Mathlib/Order/Defs/LinearOrder.lean','lemma le_of_not_gt')]:need(token in read(file),'source declaration '+token)
print(json.dumps({'pinned_input_files':len(pins),'exact_import_block_delta':True,'selected_drafts':len(headers),'direct_frontier':len(sel['frontier']),'project_order_and_tactic_import_paths_checked':len(paths),'scope':'bounded lexical source paths only; full import closure, theorem elaboration and providers not checked'},sort_keys=True,indent=2))
