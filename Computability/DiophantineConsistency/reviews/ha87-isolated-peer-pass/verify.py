from pathlib import Path
import json,hashlib,shutil
A=Path('/tmp/ha87-focused-validator-rebase-6fpta95z');P=Path('/tmp/ha87-focused-validator-rebase-q6geuvc7');F=Path('/tmp/ha87-frozen-peer-mys9nrrb');O=Path('Computability/DiophantineConsistency/reviews/ha87-isolated-peer-pass');O.mkdir(parents=True,exist_ok=True)
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
anchors={str(p):h(p) for p in [A/'state.json',P/'state.json',F/'manifest.json',F/'driver.py',F/'graph.json',F/'overlap-plan.json']};a=json.loads((A/'state.json').read_text());p=json.loads((P/'state.json').read_text());m=json.loads((F/'manifest.json').read_text());assert a['status']==p['status']=='PASS';assert len(a['records'])==len(p['records'])==85;assert all(r['verified'] and not r.get('reused_from') for r in a['records']+p['records']);assert h(A/'state.json')==m['author_final_state_sha256'];ar={r['module']:r for r in a['records']};differences=[]
def normalize(items,root):
 out={}
 for q,v in items.items():
  path=Path(q)
  try:k='overlay/'+str(path.relative_to(root/'lib'))
  except ValueError:k='package/'+str(path.relative_to('/tmp/ha87-full-source-jrvxi6bb/package-lib'))
  out[k]=v
 return out
for r in p['records']:
 old=ar[r['module']]
 for key in ['source_sha256','dependency_hashes','object_sha256','log_sha256']:
  if r[key]!=old[key]:differences.append((r['module'],key))
 if normalize(r['dependency_companions'],P)!=normalize(old['dependency_companions'],A):differences.append((r['module'],'dependency_companions'))
 for root,row in [(A,old),(P,r)]:
  assert h(root/'lib'/(row['module'].replace('.','/')+'.olean'))==row['object_sha256'];assert h(root/'logs'/row['log_file'])==row['log_sha256'];assert h(root/'logs'/row['source_snapshot'])==row['source_sha256']
assert not differences,differences
for k in ['source_hashes','current_ha_source_hashes','historical_boundary_objects','model_only_inherited_objects','package_audit_state_sha256','inherited_zf_object']:assert a[k]==p[k],k
for rel,digest in p['historical_boundary_objects'].items():assert h(P/'lib'/rel)==digest
for n,digest in p['model_only_inherited_objects'].items():assert h(P/'lib'/(n.replace('.','/')+'.olean'))==digest
assert h(P/'lib/ZF/Zf.olean')==p['inherited_zf_object']
for n,row in m['source_modules'].items():assert h(F/'tree'/row['path'])==row['sha256']
for q,digest in anchors.items():assert h(q)==digest
shutil.copyfile(P/'state.json',O/'peer-state.json');(O/'peer-logs').mkdir(exist_ok=True)
for r in p['records']:shutil.copyfile(P/'logs'/r['log_file'],O/'peer-logs'/(r['module'].replace('.','_')+'.log'))
result={'author_state_sha256':h(A/'state.json'),'peer_state_sha256':h(P/'state.json'),'frozen_manifest_sha256':h(F/'manifest.json'),'rows':len(p['records']),'peer_reused_rows':0,'differences':differences,'historical_boundary_objects':len(p['historical_boundary_objects']),'model_only_boundary_objects':len(p['model_only_inherited_objects']),'frozen_sources':len(m['source_modules']),'inherited_zf_sha256':p['inherited_zf_object'],'qualification':'pre-merge frozen source snapshot; HA/ZF/Foundation and package-transitive ancestry remains inherited'};(O/'comparison.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',result,flush=True)
