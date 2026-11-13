#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-p73-provider-preflight'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'c4326734734ddb0bd0e011073b0ec6b2ede74e5ecf61676c6268db8acefa1598','inspect.py':'67ab841e465f8923c8f3c65e07d93fa055dbfea8e6f1f745ad79442786c097b7','observation.json':'f37f6add7288d06a4e1ba60b97bc0ea5c00eeac13c5372bdceea4174c88bdae5'}.items():assert sha(p/n)==h
frozen=json.loads((p/'observation.json').read_text())
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'inspect.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr;fresh=json.loads(r.stdout)
volatile={'tmp_free_bytes','head_before','head_after','head_changed','source_head_issues'}
assert {k:v for k,v in frozen.items() if k not in volatile}=={k:v for k,v in fresh.items() if k not in volatile}
assert fresh['status']=='READ_ONLY_OBSERVATION_NOT_BUILD_READINESS' and not fresh['recorded_route_issues']
assert fresh['inspector_sha256']==sha(p/'inspect.py')
for name,project,p72 in [('graph',2,2),('endpoint',7,6),('direct_model_sketch',6,6)]:
 c=fresh[name];assert len(c['project'])==project and len(c['p72_frontier'])==p72 and len(c['external'])==1 and not c['base_frontier'] and not c['unresolved']
 assert set(c['external'])=={'Mathlib.Tactic.LinearCombination'}
 # A distinct pass over each current source's explicit import lines and a
 # topological ordering check; this is still not Lean's dependency parser.
 order=c['topological_order'];assert len(order)==len(set(order))==project and set(order)==set(c['project']);pos={n:i for i,n in enumerate(order)}
 for n,row in c['project'].items():
  src=repo/row['source'];assert sha(src)==row['source_sha256']
  imports=[]
  for line in src.read_text().splitlines():
   m=re.match(r'^\s*(?:public\s+)?import\s+([^\n-]+)',line)
   if m:imports.extend(m[1].split())
  assert imports==row['imports']
  for d in imports:
   if d in pos:assert pos[d]<pos[n]
   else:assert d in c['p72_frontier'] or d in c['base_frontier'] or d in c['external']
prefix='DiophantineConsistency.Compact44.'
assert set(fresh['graph']['project'])=={prefix+'FreeJ13',prefix+'P73Graph'}
assert set(fresh['endpoint']['project'])=={prefix+x for x in ('FreeJ13','P73Graph','FreeJ13Halt','P73Halt','P73ConvZero','P73Converse','IPRAPositive73')}
assert set(fresh['direct_model_sketch']['project'])==set(fresh['endpoint']['project'])-{prefix+'IPRAPositive73'}
assert fresh['graph_recorded_route_counts']=={'p72_objects':13,'base_objects':17}
assert fresh['recorded_p72_trace']=={'unique_project_objects':679,'direct_edges_checked':1997,'direct_companion_guards_checked':59910}
assert fresh['recorded_base_trace']=={'unique_project_objects':918,'direct_edges_checked':2647,'companion_guards_checked':20230}
# Independently check the project-table coverage and the exceptional external
# Foundation route, which must not be promoted into the project build root.
survey=json.loads((base/'research/p72-current-base-source-survey/result.json').read_text());base_state=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_text());p72=Path('/tmp/p72-current-base-extension-attempt02-20261105');order=survey['extension_order'];base_names={x['module'] for x in base_state['records']};assert base_state['status']=='PASS' and len(base_names)==1000 and len(order)==681
assert len(survey['project_sources'])==1599 and set(survey['project_sources']) <= set(order)|base_names
module='DiophantineConsistency.Compact44.CompactControllerTriangle';r=json.loads((p72/'rows'/f'{order.index(module):04d}.json').read_text());name='Foundation.FirstOrder.Arithmetic.IOpen.Basic';entry=r['dependencies'][name];assert name not in set(order)|base_names and name not in survey['project_sources'];path=Path(entry['path']);assert path.is_file() and str(path.resolve())==entry['realpath'] and sha(path)==entry['sha256'] and '/package-lib/' in str(path)
# Match actual child objects and identical source across the failed parents.
collision=fresh['failed_parent_object_collision'];m='DiophantineConsistency.ModelDifferenceRing';i=order.index(m);row=json.loads((p72/'rows'/f'{i:04d}.json').read_text());p72obj=p72/'lib'/Path(m.replace('.','/')+'.olean');assert sha(p72obj)==row['object_sha256']==collision['p72_object_sha256']
hashes={sha(p72obj)}
for label in ('03','04'):
 s=json.loads((base/f'research/current14-coherent-extension-refactor-retry{label}-runner/attempt01/state.json').read_text());assert s['status']=='FAILED';x=[x for x in s['rows'] if x.get('module')==m];assert len(x)==1;x=x[0];assert x['source_sha256']==row['source_sha256']==collision['source_sha256'] and x['compile']['exit']==0
 obj=Path(collision['failed_parent_children'][label]['object']);assert sha(obj)==x['object_sha256']==collision['failed_parent_children'][label]['object_sha256'];hashes.add(sha(obj))
assert len(hashes)==3
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','graph_source_cut':2,'endpoint_source_cut':7,'unimplemented_sketch_source_cut':6,'p72_observed_objects':679,'base_observed_objects':918,'project_source_table_coverage':1599,'foundation_external_exception':name,'distinct_model_difference_objects':len(hashes),'frozen_tmp_free_bytes':frozen['tmp_free_bytes'],'fresh_tmp_free_bytes':fresh['tmp_free_bytes'],'scope':'Recorded routes and line-parsed source observations only, not a Lean build or authenticated package/dynamic closure.'},indent=2))
