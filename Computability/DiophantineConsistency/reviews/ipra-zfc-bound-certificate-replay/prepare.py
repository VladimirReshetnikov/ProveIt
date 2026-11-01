#!/usr/bin/env python3
"""Freeze the witness-bound certificate refresh on the passed postmerge peer."""
from pathlib import Path
import hashlib,json,re,shutil
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent
OLD=ROOT/'Computability/DiophantineConsistency/reviews/ipra-zfc-bound-postmerge-replay'
PARENT=Path('/tmp/ipra-induction-nozero-upa7appl');PROJECT=ROOT/'Computability/DiophantineConsistency/Lean';ZFC=ROOT/'Logic/Interpretability/ZFCinPA/Lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=json.loads((OLD/'manifest.json').read_text());state=json.loads((PARENT/'state.json').read_text());assert state['status']=='PASS' and len(state['records'])==58
assert state['manifest_sha256']==sha(OLD/'manifest.json')
assert all(r['exit']==0 and sha(PARENT/'lib/DiophantineConsistency'/(r['module']+'.olean'))==r['object_sha256'] and sha(PARENT/'logs'/(r['module']+'.log'))==r['log_sha256'] for r in state['records'])
assert all(sha(PARENT/'lib/DiophantineConsistency'/(n+'.olean'))==h for n,h in old['parent_objects'].items())
seen={};edges={};todo=['DiophantineConsistency.IPRAZFCRefutationBoundGGChecks']
while todo:
 n=todo.pop()
 if n in seen:continue
 rel=Path(*n.split('.')).with_suffix('.lean');p=next((d/rel for d in [PROJECT,ZFC] if (d/rel).is_file()),None)
 if p is None:continue
 seen[n]=p;edges[n]=re.findall(r'^import\s+([^\s]+)',p.read_text(),re.M);todo.extend(edges[n])
assert len(seen)==306
seed={'DiophantineConsistency.PRAConBForward','DiophantineConsistency.PRAWitnessBoundCertificate','DiophantineConsistency.PRAWitnessZFCRefutationBound'}
assert seed<=seen.keys()
while True:
 x=seed|{n for n,v in edges.items() if set(v)&seed}
 if x==seed:break
 seed=x
assert len(seed)==6 and all(n.startswith('DiophantineConsistency.') for n in seed)
order=[];visiting=set();visited=set()
def visit(n):
 if n in visited:return
 assert n not in visiting
 visiting.add(n)
 for d in edges[n]:
  if d in seed:visit(d)
 visiting.remove(n);visited.add(n);order.append(n.removeprefix('DiophantineConsistency.'))
for n in sorted(seed):visit(n)
parent_names=(set(old['parent_objects'])|set(old['order']))-set(order)
objects={n:sha(PARENT/'lib/DiophantineConsistency'/(n+'.olean')) for n in sorted(parent_names)}
for n in seed:
 for d in edges[n]:
  if d.startswith('DiophantineConsistency.') and d not in seed:assert d.removeprefix('DiophantineConsistency.') in objects,d
sources=dict(old['workspace_sources']);excluded=dict(old['excluded_historical_broad_source_guards'])
for rel,previous in list(sources.items()):
 current=sha(ROOT/rel)
 if current!=previous:
  assert rel.endswith('/PRAWitnessZFCRefutationBound.lean'),rel
  sources[rel]=current
for n,p in seen.items():sources[str(p.relative_to(ROOT))]=sha(p)
for rel in list(excluded):
 if rel.endswith('/PRAConBForward.lean'):
  assert rel in sources;del excluded[rel]
frozen=PACKET/'frozen/DiophantineConsistency';frozen.mkdir(parents=True,exist_ok=True)
for n in order:shutil.copyfile(PROJECT/'DiophantineConsistency'/(n+'.lean'),frozen/(n+'.lean'))
m={'parent':str(PARENT),'parent_state_sha256':sha(PARENT/'state.json'),'lean':old['lean'],'lean_sha256':old['lean_sha256'],'package_path':old['package_path'],'workspace_sources':sources,'excluded_historical_broad_source_guards':excluded,'parent_objects':objects,'external_objects':old['external_objects'],'order':order,'suffix_sources':{n:sha(frozen/(n+'.lean')) for n in order},'current_declared_project_closure':{n:sha(p) for n,p in sorted(seen.items())},'scope':'Six-module certificate-refactor rebuild of the translated ZFC refutation bound over the passed 58-module peer. Current workspace sources, selected parent objects and recorded external objects are guarded; inherited project, Foundation, ZFC and package source/object ancestry remains historical. No ordinary native consistency claim.'}
(PACKET/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');print('frozen',len(order),'suffix,',len(objects),'parent objects,',len(sources),'workspace source guards; order',order)
