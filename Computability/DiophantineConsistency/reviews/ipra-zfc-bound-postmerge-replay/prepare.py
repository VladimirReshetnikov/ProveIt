#!/usr/bin/env python3
"""Freeze the post-merge bound suffix over an authenticated historical parent."""
from pathlib import Path
import hashlib, json, re, shutil
ROOT=Path(__file__).resolve().parents[4]
PACKET=Path(__file__).resolve().parent
OLD=ROOT/'Computability/DiophantineConsistency/reviews/ipra-zfc-refutation-bound-gg-replay'
PARENT=Path('/tmp/ipra-induction-nozero-nra7kfs5')
PROJECT=ROOT/'Computability/DiophantineConsistency/Lean'
ZFC=ROOT/'Logic/Interpretability/ZFCinPA/Lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=json.loads((OLD/'manifest.json').read_text()); state=json.loads((PARENT/'state.json').read_text())
assert state['status']=='PASS' and len(state['records'])==len(old['order'])==44
assert state['manifest_sha256']==sha(OLD/'manifest.json')
assert all(r['exit']==0 and sha(PARENT/'lib/DiophantineConsistency'/(r['module']+'.olean'))==r['object_sha256'] and sha(PARENT/'logs'/(r['module']+'.log'))==r['log_sha256'] for r in state['records'])
assert all(sha(PARENT/'lib/DiophantineConsistency'/(n+'.olean'))==v for n,v in old['parent_objects'].items())
seen={};edges={};todo=['DiophantineConsistency.IPRAZFCRefutationBoundGGChecks']
while todo:
 n=todo.pop()
 if n in seen:continue
 rel=Path(*n.split('.')).with_suffix('.lean');p=next((d/rel for d in [PROJECT,ZFC] if (d/rel).is_file()),None)
 if p is None:continue
 seen[n]=p;edges[n]=re.findall(r'^import\s+([^\s]+)',p.read_text(),re.M);todo.extend(edges[n])
assert len(seen)==297
seeds={'DiophantineConsistency.PRAWitnessCalculus','DiophantineConsistency.PRARewritingWitnessBound'}
assert seeds<=seen.keys()
cone=seeds
while True:
 following=cone|{n for n,d in edges.items() if set(d)&cone}
 if following==cone:break
 cone=following
selected=cone|{'DiophantineConsistency.'+n for n in old['order']}
assert len(cone)==57 and len(selected)==58
assert 'DiophantineConsistency.PRAConBForward' not in seen
assert 'DiophantineConsistency.PRAWitnessDerivation' not in seen
assert all(n.startswith('DiophantineConsistency.') for n in selected)
order=[];visiting=set();visited=set()
def visit(n):
 if n in visited:return
 assert n not in visiting
 visiting.add(n)
 for d in edges[n]:
  if d in selected:visit(d)
 visiting.remove(n);visited.add(n);order.append(n.removeprefix('DiophantineConsistency.'))
for n in sorted(selected):visit(n)
parent_names=set(old['parent_objects'])|set(old['order'])
parent_names-=set(order)
objects={n:sha(PARENT/'lib/DiophantineConsistency'/(n+'.olean')) for n in sorted(parent_names)}
for n in selected:
 for d in edges[n]:
  if d.startswith('DiophantineConsistency.') and d not in selected:
   assert d.removeprefix('DiophantineConsistency.') in objects, d
sources=dict(old['workspace_sources']);excluded=dict(old['excluded_historical_broad_source_guards'])
for rel,prior in list(sources.items()):
 current=sha(ROOT/rel)
 if current!=prior:
  if rel.endswith('/PRAConBForward.lean'):
   excluded[rel]={'previous_sha256':prior,'current_sha256':current,'reason':'outside current endpoint declared-import closure'};del sources[rel]
  else:
   assert rel.endswith('/PRAWitnessCalculus.lean'),rel
   sources[rel]=current
for n,p in seen.items():sources[str(p.relative_to(ROOT))]=sha(p)
frozen=PACKET/'frozen/DiophantineConsistency';frozen.mkdir(parents=True,exist_ok=True)
for n in order:shutil.copyfile(PROJECT/'DiophantineConsistency'/(n+'.lean'),frozen/(n+'.lean'))
manifest={'parent':str(PARENT),'parent_state_sha256':sha(PARENT/'state.json'),'lean':old['lean'],'lean_sha256':old['lean_sha256'],'package_path':old['package_path'],'workspace_sources':sources,'excluded_historical_broad_source_guards':excluded,'parent_objects':objects,'external_objects':old['external_objects'],'order':order,'suffix_sources':{n:sha(frozen/(n+'.lean')) for n in order},'current_declared_project_closure':{n:sha(p) for n,p in sorted(seen.items())},'scope':'58-module post-merge declared-source rebuild of the exact translated ZFC refutation bound over the accepted historical hbound peer. It guards current source hashes, selected parent objects and recorded external objects; it does not recompile the entire project, Foundation, ZFC or package ancestry, or prove ordinary native consistency.'}
(PACKET/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print('frozen',len(order),'suffix,',len(objects),'parent objects,',len(sources),'workspace source guards')
