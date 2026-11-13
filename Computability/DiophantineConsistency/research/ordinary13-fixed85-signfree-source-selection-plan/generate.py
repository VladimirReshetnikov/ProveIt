from pathlib import Path
from hashlib import sha256
from collections import deque,defaultdict
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-signfree-source-selection-plan')
manifest_path=Path('research/ordinary13-fixed85-native-composition-draft/manifest.json')
repair=Path('research/ordinary13-signfree-omega-repair-draft/ResidueSignFreePowerRepaired.lean.src')
old=Path('research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src')
assert sha256(manifest_path.read_bytes()).hexdigest()=='a4934426329ffedef443a7b6a95bd5fd09d5210c8c9014fb522deed82e65c05e'
assert sha256(repair.read_bytes()).hexdigest()=='dfb531049c859c2f6bd320a7569e1dcb69a9c9f6ddb28f1f8fcc70eb53537c3b'
assert sha256(old.read_bytes()).hexdigest()=='1c6935eda3ce9ae05d257957d7e2d8f5f3786386aaf618d5a480036113c8bb92'
m=json.loads(manifest_path.read_text()); nodes=m['local_modules']; module='ResidueSignFreePower'
assert len(nodes)==1354 and m['root']=='Fixed85Endpoint' and nodes[module]['path']==str(old)
def imports(p):
 out=[]
 for line in p.read_text().splitlines():
  match=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$',line)
  if match:out.extend(match.group(1).split())
 return out
newimp=imports(repair);assert newimp==['DiophantineConsistency.ArithmeticPellPowerRecovery','Mathlib.Tactic.NormNum','Mathlib.Tactic.Ring']
assert nodes[module]['imports']==['DiophantineConsistency.ArithmeticPellPowerRecovery','Mathlib.Tactic.Omega']
selected={}
for n,entry in sorted(nodes.items()):
 p=repair if n==module else Path(entry['path']); data=p.read_bytes(); deps=imports(p)
 if n!=module:
  assert sha256(data).hexdigest()==entry['sha256'] and deps==entry['imports'],n
 selected[n]={'source':str(p),'sha256':sha256(data).hexdigest(),'imports':deps,'selection':'explicit_replacement' if n==module else 'pinned_manifest'}
assert selected[module]['source']!=nodes[module]['path']
# Reachability and ordering are lexical, not Lean elaboration.
reachable=set();front=set();q=deque([m['root']])
while q:
 n=q.popleft()
 if n in reachable or n in front:continue
 if n not in selected:front.add(n);continue
 reachable.add(n);q.extend(selected[n]['imports'])
assert reachable==set(selected)
expected=(set(m['external_frontier'])-{'Mathlib.Tactic.Omega'})|{'Mathlib.Tactic.NormNum','Mathlib.Tactic.Ring'}
assert front==expected and len(front)==93
order=m['dependency_first_order'];assert len(order)==len(selected) and set(order)==set(selected)
pos={n:i for i,n in enumerate(order)}
for n,e in selected.items():
 for dep in e['imports']:
  if dep in selected:assert pos[dep]<pos[n],(n,dep)
reverse=defaultdict(set)
for n,e in selected.items():
 for dep in e['imports']:
  if dep in selected:reverse[dep].add(n)
assert reverse[module]=={'ResidueQBalanceGraph'}
affected={module};q=deque([module])
while q:
 for n in reverse[q.popleft()]:
  if n not in affected:affected.add(n);q.append(n)
assert len(affected)==38 and m['root'] in affected
result={'root':m['root'],'local_module_count':len(selected),'external_frontier_count':len(front),
 'external_frontier':sorted(front),'selected_sources':selected,'dependency_first_order':order,
 'replacement':{'logical_module':module,'selected_source':str(repair),'selected_sha256':sha256(repair.read_bytes()).hexdigest(),
  'excluded_original_source':str(old),'excluded_original_sha256':sha256(old.read_bytes()).hexdigest(),
  'old_imports':nodes[module]['imports'],'new_imports':newimp,'direct_lexical_consumers':sorted(reverse[module]),
  'affected_reverse_order':[n for n in order if n in affected]},
 'collision_policy':'One selected source per exact logical module; exclude original ResidueSignFreePower provider and all conflicting source/object copies from any future overlay; identical bytes alone do not authenticate objects. No provider roots or objects are selected here.',
 'scope':'Deterministic lexical source selection only; no source copy, source rewrite, external/transitive scan, collision authentication, Lean build or axiom report.'}
output=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode();target=D/'selection.json'
if '--write' in sys.argv:target.write_bytes(output)
else:assert target.read_bytes()==output
print(json.dumps({'selection_sha256':sha256(output).hexdigest(),'local_modules':len(selected),'external_frontier':len(front),'replacement_count':1,'affected_local_modules':len(affected),'omega_direct_frontier_removed':True,'sources_copied':False,'lean_executed':False},sort_keys=True,indent=2))
