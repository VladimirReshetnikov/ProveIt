from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-magnitude-modelarithmetic-selection'); BASE=Path('research/current2011-shear72-joint-ipra-source-plan/selection.json')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
old=Path('research/current2011-shear72-reverse-magnitude-draft/Shear72ReverseMagnitude.lean.src').read_text();new=(D/'Shear72ReverseMagnitude.lean.src').read_text()
edits=[('import DiophantineConsistency.ZRows.CoprimeSquares','import DiophantineConsistency.ModelArithmetic'),('open ModelDifferenceRing ZRowsCoprimeSquares','open ModelDifferenceRing'),('obtain ⟨n,habs⟩ := abs_eq_ι z','obtain ⟨n,habs⟩ := nonneg_iff.mp (abs_nonneg z)')]
for a,b in edits:
 assert old.count(a)==1,a
 old=old.replace(a,b,1)
assert old==new
model=Path('Lean/DiophantineConsistency/ModelArithmetic.lean').read_text();diff=Path('Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text();cop=Path('Lean/DiophantineConsistency/ZRows/CoprimeSquares.lean').read_text()
assert 'import DiophantineConsistency.ModelDifferenceRing' in model
assert 'theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in diff
assert 'theorem abs_eq_ι (A : DiffRing V) : ∃ a : V, |A| = ι a := nonneg_iff.mp (abs_nonneg A)' in cop
oldsel=json.loads(BASE.read_text());actual=json.loads((D/'selection.json').read_text());name='DiophantineConsistency.Shear72ReverseMagnitude'
expected=json.loads(BASE.read_text());p=D/'Shear72ReverseMagnitude.lean.src'
expected['drafts'][name]={'path':str(p),'sha256':sha256(p.read_bytes()).hexdigest(),'imports':['DiophantineConsistency.ModelArithmetic']}
expected['frontier'].pop('DiophantineConsistency.ZRows.CoprimeSquares')
p=Path('Lean/DiophantineConsistency/ModelArithmetic.lean');expected['frontier']['DiophantineConsistency.ModelArithmetic']={'kind':'project-source-frontier','path':str(p),'sha256':sha256(p.read_bytes()).hexdigest()}
assert actual==expected
for n,info in actual['drafts'].items():
 p=Path(info['path']);assert sha256(p.read_bytes()).hexdigest()==info['sha256'],n
 assert re.findall(r'^import\s+(\S+)',p.read_text(),re.M)==info['imports'],n
for n,info in actual['frontier'].items():
 if info['kind']!='external-unexamined':assert sha256(Path(info['path']).read_bytes()).hexdigest()==info['sha256'],n
active=set();seen=set();order=[];used=set()
def visit(n):
 if n in seen:return
 assert n not in active,n
 active.add(n)
 for dep in actual['drafts'][n]['imports']:
  if dep in actual['drafts']:visit(dep)
  else:assert dep in actual['frontier'],dep;used.add(dep)
 active.remove(n);seen.add(n);order.append(n)
visit('DiophantineConsistency.Shear72JointIPRA');assert seen==set(actual['drafts']) and used==set(actual['frontier'])
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'selection_sha256':sha256((D/'selection.json').read_bytes()).hexdigest(),'exact_source_substitutions':len(edits),'selected_drafts':len(seen),'direct_frontier_dropped':'DiophantineConsistency.ZRows.CoprimeSquares','direct_frontier_added':'DiophantineConsistency.ModelArithmetic','draft_topological_order':order,'transitive_provider_audited':False,'lean_executed':False},sort_keys=True,indent=2))
