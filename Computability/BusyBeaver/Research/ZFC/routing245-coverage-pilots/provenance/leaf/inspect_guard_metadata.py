"""Independent static inventory of guard literals and existing parents; never import/run guard."""
from pathlib import Path
import ast,hashlib,json,re,difflib
B=Path('/tmp/zfc-routing245-lean/coverage-pilots');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=Path(p).stat().st_size)
g=B/'check-pilots.py';tree=ast.parse(g.read_text());const={}
for n in tree.body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:const[n.targets[0].id]=ast.literal_eval(n.value)
  except (ValueError,TypeError):pass
assert const['MANIFEST_SHA']==sha(B/'pilot-plan.json')
assert const['GENERATOR_SHA']==sha(B/'prepare_pilots.py')
selected={};parents=[];files={};snapshots=[];evidence={}
for label,(path,pin,module,probes,callers) in const['PARENTS'].items():
 p=Path(path);p=p if p.is_absolute()else R/p;assert sha(p)==pin;d=json.loads(p.read_text())
 assert d['status']=='PASS' and d['prepare_only'] is False and d['before']==d['after']
 assert (d['named_axiom_probes'],d['callers'])==(probes,callers)
 assert d['only_standard_axioms'] and d['source_object_recorded_before_audit'] and d['all_fresh_objects_unchanged_after_audit']
 assert [x['label']for x in d['commands']]==['source','audit'] and all(x['exit_code']==0 for x in d['commands'])
 C=Path(d['compiler']['path']);assert sha(C)==const['COMPILER_SHA']==d['compiler']['sha256'];files[str(C.resolve())]=sha(C)
 actual={x['module']:x for x in d['actual_first_providers']}
 rows=d['reused_modules'].copy();f=d['fresh_modules'][0]
 assert f['module']==module and all(d['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256'])
 for role in ['source','audit']:
  x=d[role]
  assert sha(x['path'])==sha(x['snapshot'])==x['sha256']==d['before'][x['path']]==d['after'][x['path']]
  files[str(Path(x['path']).resolve())]=x['sha256'];files[str(Path(x['snapshot']).resolve())]=x['sha256']
 rows.append(dict(module=module,source=d['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256']))
 actual[module]=d['fresh_first_provider_before_audit']
 for x in rows:
  m=x['module'];o=Path(x['object']).resolve();s=Path(x['source']).resolve()
  assert sha(o)==x['object_sha256'] and sha(s)==x['source_sha256']
  a=actual[m];first=Path(a.get('actual_first',a.get('path'))).resolve()
  assert first==o and a['sha256']==x['object_sha256']
  for k in ['source','object']:
   if not(m==module and k=='object'):assert d['before'][x[k]]==d['after'][x[k]]==x[k+'_sha256']
  z=dict(x,source=str(s),object=str(o),selected_parent_record=desc(p))
  if m in selected:assert all(selected[m][k]==z[k]for k in ['source_sha256','object_sha256'])
  else:selected[m]=z
  files[str(o)]=sha(o);files[str(s)]=sha(s)
 for tool in d['toolchain_providers']:
  assert tool['object_sha256']==const['TOOLS'][tool['module']]==sha(tool['object']);files[str(Path(tool['object']).resolve())]=sha(tool['object'])
 evidence[str(p.resolve())]=pin
 for x in d.get('provider_evidence',d.get('parent_evidence',[])):
  p1=Path(x['path']).resolve();assert sha(p1)==x['sha256'];evidence[str(p1)]=x['sha256']
 parents.append(dict(label=label,record=desc(p),module=module,reused_project_count=len(d['reused_modules']),fresh_source=f['source_sha256'],fresh_object=f['sha256'],probes=probes,callers=callers))
closure=[];visiting=set();external={'Init'}
def visit(n):
 if not n.startswith('BusyBeaver.'):
  external.add(n);return
 if n in closure:return
 assert n not in visiting;visiting.add(n)
 for child in re.findall(r'^import ([A-Za-z0-9_.]+)$',Path(selected[n]['source']).read_text(),re.M):visit(child)
 visiting.remove(n);closure.append(n)
for n in const['DIRECT']:visit(n)
assert len(closure)==22 and set(closure)==set(selected) and external==set(const['TOOLS'])
plan=json.loads((B/'pilot-plan.json').read_text());allunitfiles=[]
for unit in plan['pilots']:
 for role in ['source','audit']:
  x=unit[role];assert sha(x['path'])==x['sha256'];files[str(Path(x['path']).resolve())]=x['sha256'];allunitfiles.append(x)
for x in plan['inputs']:
 assert sha(x['path'])==x['sha256'];files[str(Path(x['path']).resolve())]=x['sha256']
for p in [g,B/'pilot-plan.json',B/'prepare_pilots.py']:files[str(p.resolve())]=sha(p)
files.update(evidence)
# Two fresh per-unit source/audit snapshots are additionally included by the guard.
inv=dict(status='STATIC_SOURCE_PROVIDER_INVENTORY_NOT_PREPARED',guard=desc(g),reviewer=desc(Path(__file__)),
         adapted_guard=desc(Path('/tmp/zfc-routing245-lean/site/check.py')),serial_policy_reference=desc(Path('/tmp/zfc-routing245-lean/source-bisim-production/check-chunks-v3.py')),
         parent_records=parents,selected_providers=[selected[n]for n in closure],project_count=22,external_boundaries=sorted(external),
         current_existing_input_count=len(files),expected_per_unit_inputs_including_two_fresh_snapshots=len(files)+2,current_existing_inputs=files,
         frozen_order=const['ORDER'],unit_count=7,guards=9,total_probes=14,total_callers=25,
         precompiler_failure_policy='Batch distinguishes a missing unit record as PREPARATION_REJECTED_BEFORE_COMPILER; no proof result fabricated.',
         commands=dict(default_leaf='python3 -B /tmp/zfc-routing245-lean/coverage-pilots/check-pilots.py --repo /home/codex/.codex/worktrees/ec20/Proofs --output /tmp/zfc-routing245-lean/coverage-pilots/first-run1',prepare_all='python3 -B /tmp/zfc-routing245-lean/coverage-pilots/check-pilots.py --repo /home/codex/.codex/worktrees/ec20/Proofs --all --prepare-only --output /tmp/zfc-routing245-lean/coverage-pilots/prepared1',all='python3 -B /tmp/zfc-routing245-lean/coverage-pilots/check-pilots.py --repo /home/codex/.codex/worktrees/ec20/Proofs --all --output /tmp/zfc-routing245-lean/coverage-pilots/all-run1'),
         guard_execution=False,compiler_execution=False,version_query=False,source_defaults_only=True,default_proof_limits=True,
         shared_seconds_per_source_audit=120,threads=1,memory_mib=4096,scope='Static literal/read-only provider inspection only. Root must execute prepare and actual proofs.')
(B/'guard-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
old=Path('/tmp/zfc-routing245-lean/site/check.py')
(B/'guard-from-site.diff').write_text(''.join(difflib.unified_diff(old.read_text().splitlines(True),g.read_text().splitlines(True),fromfile=str(old),tofile=str(g))))
print('inventory',sha(B/'guard-inventory.json'),'existing inputs',len(files),'perunit',len(files)+2)
print('guard',sha(g))
