"""Author source/metadata inspection only; never import or execute proof guard."""
from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-production');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(Path(p).resolve()),sha256=sha(p))
g=B/'check-production.py';const={}
for n in ast.parse(g.read_text()).body:
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:const[n.targets[0].id]=ast.literal_eval(n.value)
  except(ValueError,TypeError):pass
manifest=B/'sources/generation.json';gen=B/'generate_sites_routing245.py';bound=B.parent/'coverage-subtree-pilots/boundary-plan.json'
assert sha(manifest)==const['MANIFEST_SHA'] and sha(gen)==const['GENERATOR_SHA'] and sha(bound)==const['BOUNDARY_SHA']
plan=json.loads(manifest.read_text());base=json.loads(bound.read_text());providers={q['module']:q for q in base['providers']};assert len(providers)==23
files={str(p.resolve()):sha(p)for p in [g,manifest,gen,bound]};parentreviews=[]
for q in providers.values():
 for k in ('source','object'):
  assert sha(q[k])==q[k+'_sha256'];files[str(Path(q[k]).resolve())]=q[k+'_sha256']
for label,(rel,pin,module,probes,callers) in const['PARENTS'].items():
 p=Path(rel);p=p if p.is_absolute()else R/p;assert sha(p)==pin;d=json.loads(p.read_text());files[str(p.resolve())]=pin
 assert d['status']=='PASS'and d['before']==d['after']and d['source_object_recorded_before_audit']and d['all_fresh_objects_unchanged_after_audit']
 assert(d['named_axiom_probes'],d['callers'])==(probes,callers)and d['only_standard_axioms']
 assert [q['label']for q in d['commands']]==['source','audit']and all(q['exit_code']==0 for q in d['commands'])
 C=Path(d['compiler']['path']);assert sha(C)==const['COMPILER_SHA'];files[str(C.resolve())]=sha(C)
 actual={q['module']:q for q in d['actual_first_providers']}
 for q in d['reused_modules']:
  for k in ('source','object'):assert d['before'][q[k]]==d['after'][q[k]]==sha(q[k])==q[k+'_sha256']
  a=actual[q['module']];assert Path(a.get('actual_first',a.get('path'))).resolve()==Path(q['object']).resolve()and a['sha256']==q['object_sha256']
 f=d['fresh_modules'][0];assert f['module']==module and all(f[k]==d['source_pass_object'][k]for k in ('module','path','sha256','source_sha256'))
 a=d['fresh_first_provider_before_audit'];assert Path(a.get('actual_first',a.get('path'))).resolve()==Path(f['path']).resolve()and sha(f['path'])==a['sha256']==f['sha256']
 for role in ('source','audit'):
  q=d[role];assert sha(q['path'])==sha(q['snapshot'])==q['sha256']==d['before'][q['path']]==d['after'][q['path']]
  files[str(Path(q['path']).resolve())]=q['sha256'];files[str(Path(q['snapshot']).resolve())]=q['sha256']
 for ref in d.get('provider_evidence',d.get('parent_evidence',[])):
  assert sha(ref['path'])==ref['sha256'];files[str(Path(ref['path']).resolve())]=ref['sha256']
 for t in d['toolchain_providers']:
  assert sha(t['object'])==t['object_sha256']==const['TOOLS'][t['module']];files[str(Path(t['object']).resolve())]=t['object_sha256']
 parentreviews.append(dict(label=label,record=desc(p),fresh_source=d['source']['sha256'],fresh_object=f['sha256']))
p=R/const['COVERAGE_EVIDENCE'][0];assert sha(p)==const['COVERAGE_EVIDENCE'][1];d=json.loads(p.read_text());files[str(p.resolve())]=sha(p)
assert d['status']=='PASS'and d['before']==d['after']and(d['named_axiom_probes'],d['callers'])==(11,12)
q=next(q for q in d['reused_modules']if q['module']=='BusyBeaver.ZFC.SiteCoverage')
a=next(q for q in d['actual_first_providers']if q['module']=='BusyBeaver.ZFC.SiteCoverage')
assert Path(a['actual_first']).resolve()==Path(q['object']).resolve()and a['sha256']==q['object_sha256']
for k in ('source','object'):assert sha(q[k])==d['before'][q[k]]==d['after'][q[k]]==q[k+'_sha256']
for ref in plan['inputs']:assert sha(ref['path'])==ref['sha256'];files[str(Path(ref['path']).resolve())]=ref['sha256']
allsource={m:Path(q['source'])for m,q in providers.items()};unit_index={};pilot_receipts=[]
for u in plan['units']:
 unit_index[u['module']]=len(unit_index);allsource[u['module']]=manifest.parent/u['source']
 for role in ('source','audit'):
  p=manifest.parent/u[role];assert sha(p)==u[role+'_sha256'];files[str(p.resolve())]=sha(p)
 st=allsource[u['module']].read_text();at=(manifest.parent/u['audit']).read_text()
 assert re.findall(r'^import (\S+)$',st,re.M)==u['imports']and re.findall(r'^theorem (\w+)',st,re.M)==u['probe_names']
 assert re.findall(r'^#print axioms (\S+)$',at,re.M)==['SetTheory.BusyBeaver.ZFC.SitesRouting245.'+n for n in u['probe_names']]
 assert len(re.findall(r'^example\b',at,re.M))==u['callers']==u['probes']
for u in plan['reused_units']:
 ref=u['record'];assert sha(ref['path'])==ref['sha256'];d=json.loads(Path(ref['path']).read_text())
 assert d['status']=='PASS'and d['before']==d['after']and(d['named_axiom_probes'],d['callers'])==(1,2)
 for p,h in d['before'].items():assert sha(p)==h
 assert all(q['exit_code']==0 and Path(q['log']).read_text()==q['output']for q in d['commands'])
 assert all(d['source_pass_object'][k]==d['fresh_modules'][0][k]for k in ('module','path','sha256','source_sha256'))
 for role in ('source','audit'):assert sha(d[role]['path'])==sha(d[role]['snapshot'])==d[role]['sha256']==u[role]['sha256']
 f=d['fresh_modules'][0];a=d['fresh_first_provider_before_audit'];assert sha(f['path'])==f['sha256']==a['sha256']and Path(a['actual_first']).resolve()==Path(f['path']).resolve()
 allsource[u['full_module']]=Path(u['source']['path']);pilot_receipts.append(dict(module=u['full_module'],record=ref,fresh=f,actual_before_inputs=len(d['before'])))
assert len(unit_index)==100 and len(pilot_receipts)==3
prospective=[]
for u in plan['units']:
 closure=[];active=set();tools={'Init'}
 def visit(m):
  if not m.startswith('BusyBeaver.'):tools.add(m);return
  if m in closure:return
  assert m not in active and m in allsource;active.add(m)
  for c in re.findall(r'^import (\S+)$',allsource[m].read_text(),re.M):visit(c)
  active.remove(m);closure.append(m)
 for m in u['imports']:visit(m)
 assert tools==set(const['TOOLS'])and set(providers)<=set(closure)
 assert all(unit_index[m]<unit_index[u['module']]for m in closure if m in unit_index)
 prospective.append(dict(index=unit_index[u['module']],module=u['module'],project_count=len(closure),imports=u['imports'],project_modules=closure,
                         future_generated_provider_count=sum(m in unit_index for m in closure),future_object_paths=None,proof_status='UNBUILT'))
assert prospective[0]['project_count']==23 and prospective[-1]['project_count']==125
# These are exactly the first cut's existing inputs; future snapshots add two.
assert all(sha(p)==h for p,h in files.items())
r=dict(status='STATIC_SOURCE_PROVIDER_INVENTORY_NOT_PREPARED',guard=desc(g),inspector=desc(Path(__file__)),
 manifest=desc(manifest),generator=desc(gen),adapted_guard=desc(B.parent/'coverage-subtree-pilots/check-subtrees.py'),diff=desc(B/'guard-from-subtrees.diff'),
 base_project_count=23,base_providers=list(providers.values()),external_boundaries=sorted(const['TOOLS']),parent_reviews=parentreviews,reused_pilot_reviews=pilot_receipts,
 first_unit_existing_inputs=files,first_unit_existing_input_count=len(files),first_unit_expected_inputs_with_two_snapshots=len(files)+2,
 prospective_unit_closures=prospective,final_project_closure_count=125,
 unit_count=100,new_probes=471,new_callers=471,complete_probes=474,complete_callers=477,
 policy=dict(source_audit_shared_seconds=120,threads=1,memory_mib=4096,proof_limits='defaults',serial=True,preparation_receipt_before_source=True,
             fresh_object_before_audit=True,streamed_partial_output=True,interrupt_process_group_kill_and_wait=True,no_automatic_retry=True),
 commands=dict(prepare_first=f'python3 -B {g} --repo {R} --start 0 --count 1 --prepare-only --output {B}/prepared-first',
               actual_all=f'python3 -B {g} --repo {R} --start 0 --count 100 --output {B}/all-run1'),
 guard_execution=False,compiler_execution=False,version_query=False,simulation=False,
 scope='Static author source/literal/current-provider checks; generated object paths remain unknown until actual PASS. Complete actual coverage is not yet established.')
(B/'guard-inventory.json').write_text(json.dumps(r,indent=2)+'\n');print(sha(g));print('inventory',sha(B/'guard-inventory.json'),'first',len(files)+2,'final125')
