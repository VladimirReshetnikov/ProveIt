"""Source-only inventory. Parse guard AST literals; never import or execute guard."""
from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-subtree-pilots');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=Path(p).stat().st_size)
g=B/'check-subtrees.py';const={}
for n in ast.parse(g.read_text()).body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:const[n.targets[0].id]=ast.literal_eval(n.value)
  except (ValueError,TypeError):pass
for k,n in [('MANIFEST_SHA','subtree-plan.json'),('GENERATOR_SHA','prepare_subtrees.py'),('BOUNDARY_SHA','boundary-plan.json')]:assert const[k]==sha(B/n)
selected={};parents=[];files={};evidence={}
for label,(path,pin,module,probes,callers) in const['PARENTS'].items():
 p=Path(path);p=p if p.is_absolute()else R/p;assert sha(p)==pin;d=json.loads(p.read_text())
 assert d['status']=='PASS' and d['prepare_only'] is False and d['before']==d['after']
 assert (d['named_axiom_probes'],d['callers'])==(probes,callers)
 assert d['only_standard_axioms'] and d['source_object_recorded_before_audit'] and d['all_fresh_objects_unchanged_after_audit']
 assert [x['label']for x in d['commands']]==['source','audit'] and all(x['exit_code']==0 for x in d['commands'])
 C=Path(d['compiler']['path']);assert sha(C)==const['COMPILER_SHA']==d['compiler']['sha256'];files[str(C.resolve())]=sha(C)
 actual={x['module']:x for x in d['actual_first_providers']};rows=d['reused_modules'].copy();f=d['fresh_modules'][0]
 assert f['module']==module and all(d['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256'])
 for role in ['source','audit']:
  x=d[role];assert sha(x['path'])==sha(x['snapshot'])==x['sha256']==d['before'][x['path']]==d['after'][x['path']]
  files[str(Path(x['path']).resolve())]=x['sha256'];files[str(Path(x['snapshot']).resolve())]=x['sha256']
 rows.append(dict(module=module,source=d['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256']))
 actual[module]=d['fresh_first_provider_before_audit']
 for x in rows:
  m=x['module'];o=Path(x['object']).resolve();s=Path(x['source']).resolve();assert sha(o)==x['object_sha256'] and sha(s)==x['source_sha256']
  a=actual[m];assert Path(a.get('actual_first',a.get('path'))).resolve()==o and a['sha256']==x['object_sha256']
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
p=R/const['COVERAGE_EVIDENCE'][0];assert sha(p)==const['COVERAGE_EVIDENCE'][1];d=json.loads(p.read_text())
assert d['status']=='PASS' and d['before']==d['after'] and d['only_standard_axioms'] and (d['named_axiom_probes'],d['callers'])==(11,12)
assert d['source_object_recorded_before_audit'] and d['all_fresh_objects_unchanged_after_audit'] and d['all_input_provider_postchecks']
assert d['compiler']['sha256']==sha(C) and Path(d['compiler']['path']).resolve()==C.resolve()
assert [x['label']for x in d['commands']]==['source','audit'] and all(x['exit_code']==0 for x in d['commands'])
x=next(x for x in d['reused_modules']if x['module']=='BusyBeaver.ZFC.SiteCoverage')
a=next(x for x in d['actual_first_providers']if x['module']=='BusyBeaver.ZFC.SiteCoverage')
assert a['sha256']==x['object_sha256'] and Path(a['actual_first']).resolve()==Path(x['object']).resolve()
for k in ['source','object']:assert sha(x[k])==d['before'][x[k]]==d['after'][x[k]]==x[k+'_sha256'];files[str(Path(x[k]).resolve())]=x[k+'_sha256']
selected[x['module']]=dict(x,selected_parent_record=desc(p));evidence[str(p)]=sha(p)
parents.append(dict(label='generic_coverage_reused_provider_only',record=desc(p),module=x['module'],fresh_runtime_module_not_selected=True))
expected={x['module']:x for x in json.loads((B/'boundary-plan.json').read_text())['providers']}
assert set(expected)==set(selected)
for m,x in selected.items():assert all(x[k]==expected[m][k]for k in ['source','object','source_sha256','object_sha256'])
closure=[];visiting=set();external={'Init'}
def visit(n):
 if not n.startswith('BusyBeaver.'):external.add(n);return
 if n in closure:return
 assert n not in visiting;visiting.add(n)
 for child in re.findall(r'^import ([A-Za-z0-9_.]+)$',Path(selected[n]['source']).read_text(),re.M):visit(child)
 visiting.remove(n);closure.append(n)
for n in const['DIRECT']:visit(n)
assert len(closure)==23 and set(closure)==set(selected) and external==set(const['TOOLS'])
plan=json.loads((B/'subtree-plan.json').read_text());lit=lambda s:'['+', '.join('true'if b=='1'else'false'for b in s)+']'
for unit in plan['selected_units']:
 i=unit['index'];assert tuple(unit[k]for k in ['path','lo','hi','leaves','guards','height'])==const['EXPECTED_CUTS'][i]
 for role in ['source','audit']:
  x=unit[role];assert sha(x['path'])==x['sha256'];files[str(Path(x['path']).resolve())]=x['sha256']
 st=Path(unit['source']['path']).read_text();at=Path(unit['audit']['path']).read_text()
 assert re.findall(r'^import (\S+)$',st,re.M)==const['DIRECT']
 assert re.findall(r'^theorem (\w+)',st,re.M)==['checked'] and len(re.findall(r'^example\b',at,re.M))==2
 p=lit(unit['path']);rev=lit(unit['path'][::-1]);goal=f'allSites SiteRouting245.checkSite {rev}\n      (descend TreeRouting245.tree {p}) = true'
 assert f'theorem checked :\n    {goal} := by\n  decide +kernel\n' in st
 assert f'example : {goal} := checked' in at and f'(hl : LeafAt (descend TreeRouting245.tree {p}) Q e)'in at
 assert f'SiteRouting245.checkSite ({rev}.reverse ++ Q) e = true :='in at and f'allSites_sound SiteRouting245.checkSite hl {rev} checked'in at
for x in plan['inputs']:assert sha(x['path'])==x['sha256'];files[str(Path(x['path']).resolve())]=x['sha256']
for p in [g,B/'subtree-plan.json',B/'prepare_subtrees.py',B/'boundary-plan.json']:files[str(p.resolve())]=sha(p)
files.update(evidence)
cmd=f'python3 -B {g} --repo {R}'
inv=dict(status='STATIC_SOURCE_PROVIDER_INVENTORY_NOT_PREPARED',guard=desc(g),inspector=desc(Path(__file__)),
 adapted_guard=desc(B.parent/'coverage-pilots/check-pilots.py'),diff=desc(B/'guard-from-leaf.diff'),
 parent_records=parents,selected_providers=[selected[n]for n in closure],project_count=23,external_boundaries=sorted(external),
 current_existing_input_count=len(files),expected_per_unit_inputs_including_two_fresh_snapshots=len(files)+2,current_existing_inputs=files,
 frozen_order=const['ORDER'],unit_count=3,leaves=90,guards=117,total_probes=3,total_callers=6,
 precompiler_failure_policy='Distinguish absent verification record as PREPARATION_REJECTED_BEFORE_COMPILER; never fabricate proof result.',
 commands=dict(prepare_all=cmd+f' --all --prepare-only --output {B}/prepared1',first=cmd+f' --cut 70 --output {B}/first-run1',remaining=cmd+f' --cut 174 --cut 0 --output {B}/remaining2-run1'),
 guard_execution=False,compiler_execution=False,version_query=False,shared_seconds_per_source_audit=120,threads=1,memory_mib=4096,
 default_proof_limits=True,scope='Author static source/pattern/hash inspection only; root owns preparation and proof execution. Full236-cut metadata is informational.')
(B/'guard-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
print('guard',sha(g));print('inventory',sha(B/'guard-inventory.json'));print('existing',len(files),'perunit',len(files)+2)
