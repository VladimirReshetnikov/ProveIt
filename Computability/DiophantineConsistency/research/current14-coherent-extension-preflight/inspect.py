#!/usr/bin/env python3
"""Read-only source and recorded-direct-edge survey; does not run Lean."""
import collections,hashlib,json,os,re,shutil,subprocess,sys,tomllib
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
ROOT=Path(__file__).resolve().parents[4]
D=ROOT/'Computability/DiophantineConsistency';R=D/'research'
MANIFEST=R/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
START=Path('/tmp/current14-quoted-translated-endpoint-20261110')
START_RECEIPT=R/'current14-quoted-translated-endpoint-check/attempt01/state.json'
START_OUTER=R/'current14-quoted-translated-endpoint-check/attempt01/outer-result.json'
START_AUDIT=D/'reviews/current14-quoted-translated-endpoint-terminal-independent/check.py'
cache={}
def sha(p):
 p=Path(p)
 if p not in cache:cache[p]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[p]
def need(q,msg):
 if not q:raise RuntimeError(msg)
need(sha(MANIFEST)=='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749','fresh manifest pin')
need(sha(BASE/'state.json')=='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014','fresh build state pin')
BASE_AUDIT=D/'reviews/current14-fresh-base-independent/audit.py'
BASE_RECEIPT=D/'reviews/current14-fresh-base-independent/receipt.json'
BASE_OUTER=R/'current14-standard-fresh-rebuild-preflight/terminal-observation.json'
need(sha(BASE_AUDIT)=='896d3ec17a86eaac845ed5857ae651c1b2de92fab15850ad39e7ab71a68b239c','fresh audit pin')
need(sha(BASE_RECEIPT)=='933a86784ad8d3d006e9915bcfb7dd2fa8726df504676f7c3bd7dab466f64754','fresh receipt pin')
need(sha(BASE_OUTER)=='b930ff9d1015fa5834fe62c042566070032feaab50da4ae031aba3b2b82f2bb6','fresh outer pin')
need(json.loads(BASE_RECEIPT.read_text())['status']=='PASS_SINGLE_SOURCE_CURRENT_ARTIFACT_AUDIT' and json.loads(BASE_RECEIPT.read_text())['base_state_sha256']==sha(BASE/'state.json'),'fresh receipt scope')
need(json.loads(BASE_OUTER.read_text())['observed_session_exit']==0 and json.loads(BASE_OUTER.read_text())['build_state_sha256']==sha(BASE/'state.json'),'fresh outer scope')
need(sha(START_RECEIPT)=='65b86435269571d8b9e1439e45dd56cd8605939823d9e7e25ead6c8c8a90815b','quote state pin')
need(sha(START_OUTER)=='541e62eabc834b518b068ed5f464349d7cf82b3e7b8eed6b05d813d83e09df0d','quote outer pin')
need(sha(START_AUDIT)=='b8176adaefdc70b92ba3dcefa480e79f408ccde1a3e2395137548849bb5ff82a','quote audit pin')
need(sha(START/'state.json')==sha(START_RECEIPT),'quote state copy')
outer=json.loads(START_OUTER.read_text());need(outer['outer_exit_code']==0 and outer['state_sha256']==sha(START_RECEIPT),'quote outer receipt')
need(START_AUDIT.is_file(),'quote terminal auditor unavailable')
m=json.loads(MANIFEST.read_text());b=json.loads((BASE/'state.json').read_text());target=json.loads((START/'state.json').read_text())
need(len(m['order'])==1000 and b['status']=='PASS' and len(b['records'])==1000,'fresh base status')
need(target['status']=='PASS' and len(target['rows'])==1,'quote target status')
fresh={r['module']:r for r in b['records']};need(set(fresh)==set(m['order']),'fresh base inventory')
base_issues=[];base_input_edges=0
for name,rec in fresh.items():
 p=BASE/'lib'/Path(name.replace('.','/')+'.olean')
 if rec.get('exit')!=0 or not p.is_file() or sha(p)!=rec.get('object_sha256'):base_issues.append({'module':name,'reason':'base output missing, drift or failed exit'})
 if rec.get('source_sha256')!=m['sources'][name]['sha256']:base_issues.append({'module':name,'reason':'base source/manifest mismatch'})
 for dep,q in rec.get('direct_inputs',{}).items():
  base_input_edges+=1;f=Path(q['path'])
  if not f.is_file() or sha(f)!=q['sha256']:base_issues.append({'module':name,'dependency':dep,'reason':'base recorded input missing or drift'})
for name,guards in b.get('outputs',{}).items():
 for path,expected in guards.items():
  q=Path(path)
  if expected is None:
   if os.path.lexists(q):base_issues.append({'module':name,'path':path,'reason':'unexpected output companion'})
  elif not q.is_file() or str(q.resolve())!=expected['realpath'] or sha(q)!=expected['sha256']:base_issues.append({'module':name,'path':path,'reason':'output/companion drift'})
for path,expected in b.get('guarded_companions',{}).items():
 q=Path(path)
 if expected is None:
  if os.path.lexists(q):base_issues.append({'path':path,'reason':'unexpected input companion'})
 elif not q.is_file() or str(q.resolve())!=expected['realpath'] or sha(q)!=expected['sha256']:base_issues.append({'path':path,'reason':'input/companion drift'})
source_drift=[];source_missing=[]
for n in m['order']:
 row=m['sources'][n];p=ROOT/row['workspace_path']
 if not p.is_file():source_missing.append(n)
 elif sha(p)!=row['sha256']:source_drift.append(n)
libs=tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib'];dirs={r['name']:ROOT/r.get('srcDir','.') for r in libs}
def workspace_source(name):
 root=dirs.get(name.split('.')[0]);return root/(name.replace('.','/')+'.lean') if root else None
# Follow declared host-bridge imports through every lakefile workspace namespace.
host={};external=set();host_missing=set();todo=['DiophantineConsistency.CurrentWitnessEquivalence2011','DiophantineConsistency.ObjectCurrentEquation2011']
while todo:
 n=todo.pop()
 if n in host or n in external or n in host_missing:continue
 p=workspace_source(n)
 if p is None:external.add(n);continue
 if not p.is_file():host_missing.add(n);continue
 imports=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):imports.extend(line.split('--',1)[0].split()[1:])
 host[n]={'path':str(p.relative_to(ROOT)),'sha256':sha(p),'imports':imports};todo.extend(imports)
# Index manifests as observations to find workspace copies of research-client sources.
source_index=collections.defaultdict(set)
for f in R.rglob('source-manifest.json'):
 try:data=json.loads(f.read_text())
 except (ValueError,OSError):continue
 for r in data.get('rows',[]) if isinstance(data,dict) else []:
  if not isinstance(r,dict):continue
  n=r.get('module');h=r.get('source_sha256');s=r.get('source')
  if isinstance(n,str) and isinstance(h,str) and isinstance(s,str):
   p=Path(s);p=p if p.is_absolute() else ROOT/p
   candidates=[p,f.parent/'src'/Path(n.replace('.','/')+'.lean'),f.parent/'src'/(n.split('.')[-1]+'.lean')]
   for candidate in candidates:
    if candidate.is_file() and candidate.is_relative_to(ROOT) and sha(candidate)==h:source_index[(n,h)].add(str(candidate.relative_to(ROOT)))
# The quoted endpoint's recorded direct edges; full dynamic/package imports not covered.
row=target['rows'][0];todo=[('DiophantineConsistency.'+row['module'],START/'lib/DiophantineConsistency'/(row['module']+'.olean'),row['object_sha256'])]
seen={};byname=collections.defaultdict(set);states={};kinds=collections.Counter();issues=[];traced={};package_edges=[];quote_guard_checks=0
while todo:
 name,path,expected=todo.pop();path=Path(path).resolve()
 if not path.is_relative_to(Path('/tmp')) or path.is_relative_to(Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun')):
  
  if not path.is_file() or sha(path)!=expected:issues.append({'module':name,'path':str(path),'reason':'captured external object missing or hash drift'})
  package_edges.append({'module':name,'path':str(path),'sha256':expected});continue
 key=(name,str(path));
 if key in seen:
  if seen[key]!=expected:issues.append({'module':name,'reason':'same object route with differing expected hashes'})
  continue
 seen[key]=expected;byname[name].add(expected)
 if not path.is_file() or sha(path)!=expected:issues.append({'module':name,'path':str(path),'reason':'object missing or hash drift'});continue
 if name in fresh and fresh[name]['object_sha256']==expected:
  kinds['fresh_match_same_route' if path.is_relative_to(BASE/'lib') else 'fresh_match_other_route']+=1;continue
 if name in fresh:kinds['fresh_hash_conflict']+=1
 try:part=path.parts.index('lib');producer=Path(*path.parts[:part]);state=producer/'state.json'
 except ValueError:state=Path('/nonexistent')
 if not state.is_file():issues.append({'module':name,'path':str(path),'reason':'producer state not found'});continue
 if state not in states:
  try:states[state]=json.loads(state.read_text())
  except (ValueError,OSError):issues.append({'module':name,'reason':'producer state unreadable'});continue
 data=states[state];rows=data.get('rows') or data.get('records') or [];short=name.split('.')[-1]
 matches=[r for r in rows if r.get('module','').split('.')[-1]==short and r.get('object_sha256')==expected and (r.get('compile') or r.get('compile_run') or {}).get('exit')==0]
 if len(matches)!=1:issues.append({'module':name,'path':str(path),'reason':'no unique successful producer stage'});continue
 r=matches[0];deps_run=r.get('deps') or r.get('deps_run');compile_run=r.get('compile') or r.get('compile_run')
 if not isinstance(deps_run,dict) or deps_run.get('exit')!=0 or deps_run.get('stop_reason') is not None or deps_run.get('monitor_errors') or deps_run.get('observed_descendant_pids') or compile_run.get('stop_reason') is not None or compile_run.get('monitor_errors') or compile_run.get('observed_descendant_pids'):
  issues.append({'module':name,'reason':'producer dependency/compile run not clean'});continue
 captured_guard=r.get('direct_guard') or r.get('guard')
 if not isinstance(captured_guard,dict):issues.append({'module':name,'reason':'producer direct guard absent'});continue
 for raw,g in captured_guard.items():
  quote_guard_checks+=1;q=Path(raw)
  if g is None:
   if os.path.lexists(q):issues.append({'module':name,'path':raw,'reason':'unexpected captured companion'})
  elif not q.is_file() or str(q.resolve())!=g['realpath'] or sha(q)!=g['sha256']:issues.append({'module':name,'path':raw,'reason':'captured direct guard drift'})
 snapshot=producer/'src'/Path(name.replace('.','/')+'.lean');source_hash=r.get('source_sha256')
 if not snapshot.is_file() or sha(snapshot)!=source_hash:issues.append({'module':name,'path':str(snapshot),'reason':'source snapshot missing or drift'});continue
 current=workspace_source(name);source_choices=set(source_index.get((name,source_hash),set()))
 if current and current.is_file() and sha(current)==source_hash:source_choices.add(str(current.relative_to(ROOT)))
 if not source_choices:
  for candidate in R.rglob(short+'.lean'):
   if candidate.is_file() and sha(candidate)==source_hash:source_choices.add(str(candidate.relative_to(ROOT)))
 classification='pass_parent' if data.get('status')=='PASS' else 'partial_parent_'+str(data.get('status'))
 kinds[classification]+=1
 traced[name]={'object':str(path),'object_sha256':expected,'source_sha256':source_hash,'snapshot':str(snapshot),'workspace_source_copies':sorted(source_choices),'producer_state':str(state),'producer_state_sha256':sha(state),'parent_status':data.get('status'),'dependencies':{}}
 for dep,q in r.get('dependencies',{}).items():
  if isinstance(q,str):
   guard=(r.get('guard') or r.get('direct_guard') or {}).get(q);dep_path=Path(q)
   if not isinstance(guard,dict) or 'sha256' not in guard:issues.append({'module':name,'dependency':dep,'reason':'string dependency lacks captured guard'});continue
   dep_hash=guard['sha256'];dep_path=Path(guard.get('realpath',q))
  elif isinstance(q,dict):
   dep_path=Path(q.get('realpath',q.get('path','')));dep_hash=q.get('sha256')
   if not dep_hash:issues.append({'module':name,'dependency':dep,'reason':'dependency lacks hash'});continue
  else:issues.append({'module':name,'dependency':dep,'reason':'unsupported dependency record'});continue
  traced[name]['dependencies'][dep]={'path':str(dep_path),'sha256':dep_hash};todo.append((dep,dep_path,dep_hash))
conflicts={n:sorted(h) for n,h in byname.items() if len(h)>1}
package_byname=collections.defaultdict(set)
for r in package_edges:package_byname[r['module']].add((r['path'],r['sha256']))
package_conflicts={n:sorted(v) for n,v in package_byname.items() if len(v)>1}
package_root=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');tool_root=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
host_external_observed={};host_external_missing=[]
for n in sorted(external):
 options=[p/Path(n.replace('.','/')+'.olean') for p in (package_root,tool_root)];available=[p for p in options if p.is_file()]
 if not available:host_external_missing.append(n)
 else:
  selected=available[0];host_external_observed[n]={'path':str(selected),'realpath':str(selected.resolve()),'sha256':sha(selected)}
host_extra=set(host)-set(fresh);host_overlap=set(host)&set(fresh);quote_names=set(traced);joint=host_extra & quote_names
source_unavailable=sorted(n for n,r in traced.items() if not r['workspace_source_copies'])
head_before=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
tracked=set(subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0'))
dirty=set(subprocess.check_output(['git','diff','--name-only',head_before,'--'],cwd=ROOT,text=True).splitlines())
source_untracked=sorted(n for n,r in traced.items() if not any(p in tracked for p in r['workspace_source_copies']))
host_untracked=sorted(n for n,r in host.items() if r['path'] not in tracked)
host_dirty=sorted(n for n,r in host.items() if r['path'] in dirty)
source_without_clean_copy=sorted(n for n,r in traced.items() if not any(p in tracked and p not in dirty for p in r['workspace_source_copies']))
quote_import_mismatches=[]
for n,r in traced.items():
 declared=set()
 for line in Path(r['snapshot']).read_text().splitlines():
  if line.startswith('import '):declared.update(line.split('--',1)[0].split()[1:])
 declared.discard('Init');captured=set(r['dependencies'])-{'Init'}
 if declared!=captured:quote_import_mismatches.append({'module':n,'declared_not_captured':sorted(declared-captured),'captured_not_declared':sorted(captured-declared)})
foreign_source_mismatch=sorted(n for n,r in traced.items() if n in host and r['source_sha256']!=host[n]['sha256'])
# A proposed topological order over observed names only; this does not build them.
union_names=host_extra | quote_names
union_deps={n:set() for n in union_names}
for n in union_names:
 if n in host:union_deps[n].update(x for x in host[n]['imports'] if x in union_names)
 if n in traced:union_deps[n].update(x for x in traced[n]['dependencies'] if x in union_names)
visiting=set();visited=set();union_order=[]
def visit(n):
 if n in visited:return
 if n in visiting:raise RuntimeError('cycle in observed union imports: '+n)
 visiting.add(n)
 for dep in sorted(union_deps[n]):visit(dep)
 visiting.remove(n);visited.add(n);union_order.append(n)
for n in sorted(union_names):visit(n)
disk=shutil.disk_usage('/tmp');mem=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
result={'status':'OBSERVATION_NOT_BUILD_READINESS','scope':'Read-only point-in-time declared host-source imports and captured quoted-client direct edges. No Lean, full package/dynamic import trace, transient-mutation guard, or proof of coherent rebuild. Matching object hashes alone do not authenticate private companions or ancestry.',
 'fresh':{'modules':len(fresh),'observed_input_edges':base_input_edges,'input_companion_guards':len(b.get('guarded_companions',{})),'point_in_time_issues':base_issues,'workspace_source_drift':source_drift,'workspace_source_missing':source_missing,'base_state_sha256':sha(BASE/'state.json')},
 'host':{'modules':len(host),'fresh_overlap':len(host_overlap),'fresh_extra':len(host_extra),'fresh_extra_names':sorted(host_extra),'external_import_names':sorted(external),'external_names_new_to_fresh_manifest':sorted(external-set(m['external_modules'])),'external_observed':host_external_observed,'external_missing':host_external_missing,'untracked_source_modules':host_untracked,'source_modules_differing_from_head':host_dirty,'missing_project':sorted(host_missing),'sources':host},
 'quoted':{'observed_project_objects':len(seen),'counts':dict(kinds),'producer_states':len(states),'captured_direct_guard_checks':quote_guard_checks,'captured_external_edges':len(package_edges),'captured_external_unique':len(package_byname),'captured_external_route_conflicts':package_conflicts,'issues':issues,'namespace_object_hash_conflicts':conflicts,'declared_direct_import_mismatches':quote_import_mismatches,'traced':traced,'traced_without_workspace_source_copy':source_unavailable,'traced_without_git_tracked_source_copy':source_untracked,'traced_without_clean_head_source_copy':source_without_clean_copy,'source_disagreements_with_host':foreign_source_mismatch},
 'union':{'host_extra_and_quote_traced_names':len(joint),'host_extra_and_quote_traced':sorted(joint),'host_extra_or_quote_traced_names':len(union_names),'observed_union_topological_order':union_order,'existing_quote_extension_object_bytes':sum(Path(r['object']).stat().st_size for r in traced.values()),'existing_quote_extension_snapshot_bytes':sum(Path(r['snapshot']).stat().st_size for r in traced.values()),'host_extra_source_bytes':sum((ROOT/host[n]['path']).stat().st_size for n in host_extra)},
 'resources':{'tmp_total_bytes':disk.total,'tmp_free_bytes':disk.free,'mem_available_bytes':mem,'existing_guard_min_disk_bytes':5_000_000_000,'existing_guard_min_available_memory_bytes':10*1024**3},
 'pins':{'git_head_before':head_before,'git_head_after':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'quote_state_sha256':sha(START_RECEIPT),'quote_outer_sha256':sha(START_OUTER),'quote_terminal_auditor_sha256':sha(START_AUDIT),'lakefile_sha256':sha(ROOT/'lakefile.toml'),'manifest_sha256':sha(MANIFEST)},'script_sha256':sha(__file__)}
print(json.dumps(result,sort_keys=True,indent=2))
