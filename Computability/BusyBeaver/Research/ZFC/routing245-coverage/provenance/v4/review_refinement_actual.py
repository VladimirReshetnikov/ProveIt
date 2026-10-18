"""Independent inspection of existing four-unit evidence, without proof replay."""
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-production/v4');W=B/'refined49-run1';checks=0;pins={};rows=[]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ck(v,m='evidence mismatch'):
 global checks
 assert v,m;checks+=1
def pin(p,h):
 p=Path(p);ck(sha(p)==h,str(p));pins[str(p)]=h
pin(B/'independent-source-family-review.json','8b6b434fffcba8ef242479f451e892cb1c84486cf3d1720f12d752e0a6d6f0b7')
g=json.loads((B/'sources/generation.json').read_text());batch=json.loads((W/'batch.json').read_text());pin(W/'batch.json','a5425c0577d7deb4689ff5fc3f0e24ba1b5ffa29ab0fa17f5496529b1403c414')
ck(batch['status']=='PASS_SELECTED_UNITS'and not batch['prepare_only']and batch['selected_unit_indices']==[0,1,2,3]and batch['active_unit']is None and batch['failed_unit']is None)
for role in ['guard','manifest']:q=batch[role];pin(q['path'],q['sha256'])
objects={};total_inputs=0
for idx,row in enumerate(batch['completed_units']):
 ref=row['record'];pin(ref['path'],ref['sha256']);r=json.loads(Path(ref['path']).read_text());u=g['units'][idx]
 ck(row['unit_index']==r['unit_index']==idx and row['module']==r['module']==u['module']and r['status']=='PASS'and not r['prepare_only'])
 ck(r['before']==r['after']and(r['named_axiom_probes'],r['callers'])==(u['probes'],u['callers'])and r['warnings']=={'source':0,'audit':0})
 ck(r['limits']=={'threads':1,'memory_mebibytes':4096,'shared_wall_seconds':120,'proof_limits':'Lean defaults'})
 for flag in ['all_input_provider_postchecks','only_standard_axioms','source_object_recorded_before_audit','all_fresh_objects_unchanged_after_audit','exact_project_import_closure']:ck(r[flag])
 ck(not r['compiler_version_query_performed']and not r['dependency_build']and not r['downloads'])
 for p,h in r['before'].items():pin(p,h)
 total_inputs+=len(r['before'])
 for role in ['source','audit']:
  q=r[role];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256']);ck(q['sha256']==u[role+'_sha256'])
 ck([c['label']for c in r['commands']]==['source','audit'])
 for c in r['commands']:
  ck(c['exit_code']==0 and not c['timed_out']and not c['interrupted']and c['command'][1:3]==['-j1','-M4096']);ck(Path(c['log']).read_text()==c['output']);pin(c['log'],sha(c['log']))
 ck(sum(c['seconds']for c in r['commands'])<120)
 names=re.findall(r'^#print axioms (\S+)$',Path(r['audit']['path']).read_text(),re.M)
 reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r['commands'][1]['output'])
 actual=[dict(name=n,axioms=[a.strip()for a in aa.split(',')if a.strip()])for n,aa in reports]
 ck(len(actual)==u['probes'] and actual==r['actual_axiom_sets']and[n for n,aa in reports]==names and all(q['axioms']==['propext','Quot.sound']for q in actual))
 ck(len(re.findall(r'^example\b',Path(r['audit']['path']).read_text(),re.M))==u['callers'])
 f,=r['fresh_modules'];pin(f['path'],f['sha256']);ck(f['module']==r['module']and f['source_sha256']==r['source']['sha256'])
 ck(all(f[k]==r['source_pass_object'][k]for k in ['module','path','sha256','source_sha256'])and r['source_pass_object']['source_command_index']==0)
 first=r['fresh_first_provider_before_audit'];ck(first['module']==f['module']and first['sha256']==f['sha256']and Path(first['actual_first']).resolve()==Path(f['path']).resolve())
 cache=Path(r['LEAN_PATH']);ck((cache/Path(*r['module'].split('.'))).with_suffix('.olean').resolve()==Path(f['path']).resolve())
 prov={p['module']:p for p in r['reused_modules']};ck(len(prov)==r['project_module_count']==(26 if idx==3 else 23));seen=set()
 def dfs(path):
  for mod in re.findall(r'^import (\S+)',Path(path).read_text(),re.M):
   if not mod.startswith('BusyBeaver.'):continue
   ck(mod in prov,'unknown import '+mod)
   if mod in seen:continue
   seen.add(mod);dfs(prov[mod]['source'])
 dfs(r['source']['path']);ck(seen==set(prov))
 for mod,p in prov.items():
  pin(p['source'],p['source_sha256']);pin(p['object'],p['object_sha256']);first=next(x for x in r['actual_first_providers']if x['module']==mod)
  ck(first['sha256']==p['object_sha256']and Path(first['actual_first']).resolve()==Path(p['object']).resolve());ck((cache/Path(*mod.split('.'))).with_suffix('.olean').resolve()==Path(p['object']).resolve())
 for p in r['toolchain_providers']:pin(p['object'],p['object_sha256']);ck(Path(p['actual_first']).resolve()==Path(p['object']).resolve())
 if idx==3:
  for mod,obj in objects.items():ck(mod in prov and prov[mod]['object_sha256']==obj['sha256']and Path(prov[mod]['object']).resolve()==Path(obj['path']).resolve())
 objects[r['module']]=f
 pref=r['preparation'];pin(pref['path'],pref['sha256']);ck(pref==row['preparation']);p=json.loads(Path(pref['path']).read_text())
 ck(p['status']=='PREPARED_NOT_BUILT'and p['prepare_only']and p['commands']==[]and p['fresh_modules']==[]and p['before']==p['after']and p['all_input_provider_postchecks'])
 for path,h in p['before'].items():pin(path,h)
 for k in ['source','audit','manifest','reused_modules','actual_first_providers']:ck(p[k]==r[k])
 rows.append(dict(record=ref,module=r['module'],inputs=len(r['before']),projects=len(prov),fresh=f,probes=u['probes'],callers=u['callers'],warnings=r['warnings'],source_seconds=r['commands'][0]['seconds'],audit_seconds=r['commands'][1]['seconds']))
# Preserve the distinction between a budget timeout and the later non-timeout diagnostic.
failed=[]
for p,h,timeout in [(B.parent/'all-run1/unit013/verification.json','59e6ab1764a0062e4d272d0c6bf8af0ed7aba370eb3dab020eaeaa446bfe6a12',True),(B.parent/'v2/cut42-run1/unit000/verification.json','e4c402e883fe27e58e7caba2542a51adfee9cf97a33fdcc293b4fff8e723bab5',False),(B.parent/'v3/remaining-run1/unit008/verification.json','c000fe17683398cfedc53f5d692fa556087d5974f0316d1b96d13ee40ac173cc',False)]:
 pin(p,h);r=json.loads(p.read_text());ck(r['status']=='FAIL'and r['fresh_modules']==[]and len(r['commands'])==1 and r['commands'][0]['timed_out']==timeout)
 c=r['commands'][0];ck(Path(c['log']).read_text()==c['output']);pin(c['log'],sha(c['log']))
 for role in ['source','audit']:q=r[role];pin(q['snapshot'],q['sha256'])
 ck('TIMEOUT'in c['output']if timeout else'Error pretty printing: maximum recursion depth has been reached'in c['output'])
 failed.append(dict(path=str(p),sha256=h,source_only_failure=True,timeout=timeout,audit_not_reached=True))
out=dict(status='CLEAN_EXISTING_REFINED49_FOUR_UNIT_PASS_REVIEW',findings=[],checks=checks,reviewer_script_sha256=sha(__file__),batch=dict(path=str(W/'batch.json'),sha256=sha(W/'batch.json')),source_review=dict(path=str(B/'independent-source-family-review.json'),sha256=sha(B/'independent-source-family-review.json')),units=rows,input_references=total_inputs,unique_current_identities=len(pins),current_pins=pins,preserved_failures=failed,probes=5,callers=5,warnings=0,scope='Three actual cut49 parts and two structural joins are checked. The join module imports all three passed part objects and retains the original block49 proposition. This is not complete coverage or BinaryRouting245 or a PA equivalence.',no_proof_guard_compiler_version_simulation_execution=True)
p=B/'independent-refinement-actual-review.json';ck(not p.exists());p.write_text(json.dumps(out,indent=2)+'\n');print(p,sha(p),checks,total_inputs,len(pins))
