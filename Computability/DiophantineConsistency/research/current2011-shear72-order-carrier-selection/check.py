from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-order-carrier-selection');BASE=Path('research/current2011-shear72-private-extraction-source-selection/selection.json')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
old=Path('research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src').read_text();new=(D/'ShearOrder.lean.src').read_text()
a='import DiophantineConsistency.ModelCarrierSpheres\n';b='import DiophantineConsistency.Carrier65\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.ByContra\n'
assert old.count(a)==1 and old.replace(a,b,1)==new
core=Path('Lean/DiophantineConsistency/Carrier65.lean').read_text()
for t in ['structure Core (R : Type*)','def core (p : Fin 4 → R) (v : Fin 14 → R) : Core R','let T := v 6','let V := f ^ 2 * (c * T - rank) - c','  c : R','  f : R','  rank : R','  V : R']:assert t in core,t
lt=Path('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith.lean').read_text();front=Path('../../.lake/packages/mathlib/Mathlib/Tactic/Linarith/Frontend.lean').read_text();contra=Path('../../.lake/packages/mathlib/Mathlib/Tactic/ByContra.lean').read_text()
assert 'import Mathlib.Tactic.Linarith.Frontend' in lt and 'syntax (name := nlinarith)' in front and 'by_contra' in contra
ringdefs=Path('../../.lake/packages/mathlib/Mathlib/Algebra/Ring/Defs.lean').read_text()
ordered=Path('../../.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean').read_text()
linear=Path('../../.lake/packages/mathlib/Mathlib/Order/Defs/LinearOrder.lean').read_text()
for t in ['class CommRing']:assert t in ringdefs,t
for t in ['class IsStrictOrderedRing','mul_nonneg','sub_nonneg']:assert t in ordered,t
for t in ['class LinearOrder','lemma le_of_not_gt']:assert t in linear,t
expected=json.loads(BASE.read_text());actual=json.loads((D/'selection.json').read_text());p=D/'ShearOrder.lean.src'
expected['drafts']['ShearOrder']={'path':str(p),'sha256':sha256(p.read_bytes()).hexdigest(),'imports':['DiophantineConsistency.Carrier65','Mathlib.Tactic.Linarith','Mathlib.Tactic.ByContra']}
expected['frontier'].pop('DiophantineConsistency.ModelCarrierSpheres');p=Path('Lean/DiophantineConsistency/Carrier65.lean');expected['frontier']['DiophantineConsistency.Carrier65']={'kind':'project-source-frontier','path':str(p),'sha256':sha256(p.read_bytes()).hexdigest()}
for n in ['Mathlib.Tactic.Linarith','Mathlib.Tactic.ByContra']:expected['frontier'][n]={'kind':'external-unexamined'}
assert expected==actual
for n,i in actual['drafts'].items():
 p=Path(i['path']);assert sha256(p.read_bytes()).hexdigest()==i['sha256'],n
 assert re.findall(r'^import\s+(\S+)',p.read_text(),re.M)==i['imports'],n
for n,i in actual['frontier'].items():
 if i['kind']!='external-unexamined':assert sha256(Path(i['path']).read_bytes()).hexdigest()==i['sha256'],n
seen=set();active=set();used=set();order=[]
def visit(n):
 if n in seen:return
 assert n not in active,n
 active.add(n)
 for x in actual['drafts'][n]['imports']:
  if x in actual['drafts']:visit(x)
  else:assert x in actual['frontier'],x;used.add(x)
 active.remove(n);seen.add(n);order.append(n)
visit('DiophantineConsistency.Shear72JointIPRA');assert seen==set(actual['drafts']) and used==set(actual['frontier'])
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'selection_sha256':sha256((D/'selection.json').read_bytes()).hexdigest(),'one_import_block_delta':True,'core_projection_shapes_checked':True,'tactic_source_entrypoints_observed':True,'draft_count':len(seen),'draft_topological_order':order,'import_sufficiency_elaborated':False,'lean_executed':False},sort_keys=True,indent=2))
