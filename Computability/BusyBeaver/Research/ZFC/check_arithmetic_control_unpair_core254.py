"""Guarded actual short MP unpair and initial parameter-push/unpair composition.
Checked represented ParamPush evidence supplies 98 exact project prerequisites.
Only the new source/audit is checked; no dependency, site or bootstrap replay.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
p=argparse.ArgumentParser(description=__doc__)
for k in ('repo','dependency-root','param-push-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
for k in ('source','audit','cache','lean'):p.add_argument('--'+k,type=Path)
p.add_argument('--library-path',type=Path,action='append',default=[])
p.add_argument('--source-pass-evidence',type=Path)
p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';s=importlib.util.spec_from_file_location('zero_spare_helpers',helper);H=importlib.util.module_from_spec(s);s.loader.exec_module(H)
records=[(a.param_push_evidence.resolve(),12,22,'9134d13759d19f7ac84181a5abab2179c60e64703b4dc9edbcaa4fd98ebdc8a1','9e3777020817b27e0da625e6d1aa1c29a61983c68d74109adf577d6dd9b19a5d','098ef8d4de3d1451c35c243de0b205e512b3bbde04c3b227e7b76117945b55e7')]
C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);mods={};providers={};old=[];inherited_objects=[];historical_unused_alternatives=[]
def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
def add(q):
 q=dict(q,source=str(source(q['module'])));m=q['module']
 if a.cache:q['object']=str(a.cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))
 assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256'];inherited_objects.append(dict(q))
 if m in mods:assert mods[m]['source_sha256']==q['source_sha256']and mods[m]['object_sha256']==q['object_sha256']
 else:mods[m]=q
for E,probes,callers,ss,aa,eh in records:
 assert sha(E)==eh
 e=json.loads(E.read_text());old.append(e);assert e['status']=='PASS'and e['named_axiom_probes']==probes and e['callers']==callers and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'];assert e['source']['sha256']==ss and e['audit']['sha256']==aa
 assert e['source_object_recorded_before_audit']and e['per_command_timeout_seconds']==120
 assert[q['label']for q in e['commands']]==['source','audit']and all(q['exit_code']==0 and not q['timed_out']for q in e['commands'])
 assert e['source_pass_object']['sha256']==e['fresh_modules'][0]['sha256']and e['source_pass_object']['source_sha256']==ss
 assert sha(C)==e['compiler']['sha256']and version==e['compiler']['version']
 if 'dependencies'in e:
  for n in ('Foundation','Mathlib'):assert deps[n]['pin']==e['dependencies'][n]['pin']and deps[n]['tracked_clean']and e['dependencies'][n]['tracked_clean']
  assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
  for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
 for q in e['reused_modules']:add(q)
 assert len(e['fresh_modules'])==1;q=e['fresh_modules'][0];assert q['source_sha256']==e['source']['sha256'];add(dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256']))
 for q in e.get('same_source_object_alternatives',[])+e.get('inherited_unused_alternatives_not_rechecked',[]):
  assert q['source_sha256']==mods[q['module']]['source_sha256']and q.get('selected')is False
  historical=dict(q);historical['parent_scope']=historical.pop('scope',None)
  historical_unused_alternatives.append(dict(historical,current_check_selected=False,current_check_rehashed=False,current_scope='Inherited parent provenance only; this object is not imported or rehashed by the current check. Actual selected project providers are verified separately.'))
 for q in e['providers']:
  m=q['module']
  if m in providers:assert providers[m]['source_sha256']==q['source_sha256']and providers[m]['object_sha256']==q['object_sha256']
  else:providers[m]=dict(q)
is_tool=lambda m:m=='Init'or m.startswith(('Lean.','Std.'))
assert len(mods)==98 and set(providers)=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Arithmetic.Exponential.Exp','Foundation.FirstOrder.Arithmetic.Definability.Absoluteness'}
for m,q in providers.items():
 rel=Path(m.replace('.','/'));dep='Foundation'if m.startswith('Foundation.')else'Mathlib';q['source']=str(Path(deps[dep]['path'])/rel.with_suffix('.lean'));obj=next(p/rel.with_suffix('.olean')for p in libs if(p/rel.with_suffix('.olean')).is_file());assert sha(q['source'])==q['source_sha256']and sha(obj)==q['object_sha256'];q['object']=str(obj.resolve());q['actual_first_provider']=True
S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticControlUnpairCore254.lean'
A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_control_unpair_core254_audit.lean'
assert sha(S)=='3659b629e6e8127381f75062ab8b4b93e693c89e57e2dd8b5b9be797602df371'
assert sha(A)=='2c091567d47e3cf5c2474e1f74f57bd499f6743eaefcb929bb4c745fb1f4d38b'
module='BusyBeaver.ZFC.ArithmeticControlUnpairCore254';prefix='SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.'
imports=['BusyBeaver.ZFC.ArithmeticControlParamPush254'];assert H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[module]
seen=set();external=set();visiting=set()
def visit(m):
 if m in seen:return
 assert m in mods and m not in visiting;visiting.add(m)
 for n in H.lean_imports(Path(mods[m]['source']).read_text()):
  if n in mods:visit(n)
  else:assert n.startswith(('Foundation.','Mathlib.'))or is_tool(n);external.add(n)
 visiting.remove(m);seen.add(m)
for m in imports:visit(m)
assert seen==set(mods)and external-{n for n in external if is_tool(n)}<=set(providers)
names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);expected=['move_s2_s1', 'move_s2_main', 'body_run', 'walk_reach', 'core_run', 'mpCoreIncS2_source', 'mpCoreTestS1_source', 'mpCoreAgain_source', 'mpCoreRestoreTest_source', 'mpConstructorEntry_source', 'mp_unpair_run', 'mp_initial_pop_run'];assert names==[prefix+n for n in expected]and len(re.findall(r'^example\b',A.read_text(),re.M))==18
source_pass=None
if a.source_pass_evidence:
 E=a.source_pass_evidence.resolve();assert sha(E)=='1426d4e1640d8ddb82617a4f78df77b62eb9f4c56ac653a03ce80be8a330d05e'
 e=json.loads(E.read_text());assert e['status']=='FAIL'and len(e['commands'])==2
 sc,ac=e['commands'];assert sc['label']=='source'and sc['exit_code']==0 and not sc['timed_out']and ac['label']=='audit'and ac['exit_code']!=0 and not ac['timed_out']
 assert e['source']['sha256']==sha(S)=='3659b629e6e8127381f75062ab8b4b93e693c89e57e2dd8b5b9be797602df371'and e['audit']['sha256']=='d9ff048a1b4c9f606c6d8f79231e3cd45f3f5ffe3f7be804bfb4d163a40d69c2'
 assert e['source_object_recorded_before_audit']and e['per_command_timeout_seconds']==120
 po=e['source_pass_object'];assert po['module']==module and po['source_sha256']==sha(S)and po['source_command_index']==0 and po['sha256']=='bc71823cae6205e0e57f7bfaf7976d31dca790812933bf54f54537985b69ca88'
 assert e['compiler']['sha256']==sha(C)and e['compiler']['version']==version
 assert sc['command'][0]==e['compiler']['path']and'-M4096'in sc['command']and sc['command'][-1]==e['source']['snapshot']
 ps=Path(e['source']['snapshot']);pa=Path(e['audit']['snapshot']);assert sha(ps)==e['source']['sha256']and sha(pa)==e['audit']['sha256']
 pg=E.parent/'executed-check.py';assert sha(pg)=='d38c5862a89c50ca0f3b9e480a4a7609481f79472f8342d4dc02c83793c5a7ab'and e['before'][str('/tmp/zfc-arithmetic-control-unpair-core/check.py')]==sha(pg)
 for q in e['reused_modules']:
  z=mods[q['module']];assert z['source_sha256']==q['source_sha256']and z['object_sha256']==q['object_sha256']
 assert len(e['reused_modules'])==len(mods)
 for q in e['providers']:
  z=providers[q['module']];assert z['source_sha256']==q['source_sha256']and z['object_sha256']==q['object_sha256']
 for n in ('Foundation','Mathlib'):assert e['dependencies'][n]['pin']==deps[n]['pin']
 assert e['dependencies']['lake_manifest_sha256']==deps['lake_manifest_sha256']
 for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
 so=Path(sc['command'][sc['command'].index('-o')+1]);assert str(so)==po['path']
 so=(a.cache.resolve()/Path(module.replace('.','/')).with_suffix('.olean'))if a.cache else so
 assert sha(so)==po['sha256']
 source_pass=dict(original_record=dict(path=str(E),sha256=sha(E),status=e['status']),source_pass_command=sc,overall_failed_audit_command=ac,source_snapshot=dict(path=str(ps),sha256=sha(ps)),failed_audit_snapshot=dict(path=str(pa),sha256=sha(pa)),original_executed_guard=dict(path=str(pg),sha256=sha(pg)),object=dict(path=str(so.resolve()),sha256=sha(so)),original_source_object_recorded_before_audit=True,recorded_source_pass_object=po,object_hash_scope='Exact object hash persisted immediately after the original successful source command and before its failed audit. Rehashed unchanged for this audit-only continuation.',source_compilations_in_this_run=0)
cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(module.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for q in mods.values():
 dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
if source_pass:
 dest=cache/Path(module.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(source_pass['object']['path']).resolve())
actual=[]
for q in list(mods.values())+list(providers.values()):
 rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(p/rel for p in[cache,*libs]if(p/rel).is_file());assert sha(o)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(o),resolved=str(o.resolve()),sha256=sha(o)))
if source_pass:
 rel=Path(module.replace('.','/')).with_suffix('.olean');o=next(p/rel for p in[cache,*libs]if(p/rel).is_file());assert sha(o)==source_pass['object']['sha256'];actual.append(dict(module=module,actual_first=str(o),resolved=str(o.resolve()),sha256=sha(o),source_pass_reused=True))
toolroot=C.parent.parent/'lib/lean';tool=[]
direct_tool_imports={n for f in [S,A]+[Path(q['source'])for q in list(mods.values())+list(providers.values())]for n in H.lean_imports(f.read_text())if is_tool(n)}
for m in sorted(direct_tool_imports|{'Init','Lean.Elab.Tactic.Omega'}):
 rel=Path(m.replace('.','/')).with_suffix('.olean');ref=toolroot/rel;o=next(p/rel for p in[cache,*libs,toolroot]if(p/rel).is_file());assert sha(o)==sha(ref)
 for e in old:
  for q in e.get('toolchain_providers',[]):
   if q['module']==m:assert sha(o)==q['object_sha256']
 tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),actual_first=str(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,*[x[0]for x in records],C,S,A,ss,aa,D/'lake-manifest.json']
for q in inherited_objects+list(providers.values()):inputs.extend([Path(q['source']),Path(q['object'])])
if source_pass:
 inputs.extend(Path(source_pass[k]['path'])for k in ('original_record','source_snapshot','failed_audit_snapshot','original_executed_guard','object'))
inputs.extend(Path(q[k])for q in tool for k in ('object','toolchain_reference'));inputs=list(dict.fromkeys(p.resolve()for p in inputs));before={str(p):sha(p)for p in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,provider_evidence=[dict(path=str(x[0]),sha256=sha(x[0]))for x in records],compiler=dict(path=str(C),version=version,sha256=sha(C)),source_overridden=a.source is not None,audit_overridden=a.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),inherited_record_objects=inherited_objects,inherited_unused_alternatives_not_rechecked=historical_unused_alternatives,providers=list(providers.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct_tool_imports),actual_first_providers=actual,exact_project_import_closure=True,dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
r.update(per_command_timeout_seconds=120,source_object_recorded_before_audit=False)
r.update(reused_prior_source_pass=source_pass is not None,prior_source_pass=source_pass,source_compilations=0 if source_pass or a.prepare_only else 1)
if source_pass:
 r.update(source_object_recorded_before_audit=True,source_pass_origin='PRIOR_SOURCE_COMMAND_REUSED_FOR_THIS_AUDIT',source_pass_object=dict(module=module,path=str(cache/Path(module.replace('.','/')).with_suffix('.olean')),sha256=source_pass['object']['sha256'],source_sha256=sha(S),source_command_index=None,prior_source_command_index=0,source_pass_record=source_pass['original_record']))
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(p):sha(p)for p in inputs};assert before==after
 for q in list(mods.values())+list(providers.values())+tool:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(p/rel for p in[cache,*libs,toolroot]if(p/rel).is_file());assert sha(o)==q['object_sha256']
 if source_pass:
  o=cache/Path(module.replace('.','/')).with_suffix('.olean');assert sha(o)==source_pass['object']['sha256']
 _,d=H.dependency_libraries(D,a.library_path);assert d==deps;r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
def run(label,file,obj=None):
 cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic()
 try:cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True,timeout=120)
 except subprocess.TimeoutExpired as ex:
  def decoded(v):return v.decode(errors='replace')if isinstance(v,bytes)else(v or'')
  out=decoded(ex.stdout)+decoded(ex.stderr);(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=None,timed_out=True,timeout_seconds=120,output=out));r.update(status='FAIL',error=label+' timed out after120seconds');save();raise RuntimeError(r['error'])from ex
 out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,timed_out=False,timeout_seconds=120,output=out))
 if label=='source'and cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out:
  r.update(source_pass_object=dict(module=module,path=str(obj),sha256=sha(obj),source_sha256=sha(S),source_command_index=len(r['commands'])-1),source_object_recorded_before_audit=True)
 save();assert cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
try:
 obj=cache/Path(module.replace('.','/')).with_suffix('.olean')
 if not source_pass:run('source',ss,obj)
 oh=sha(obj);assert r['source_pass_object']['sha256']==oh;out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports);post();assert sha(obj)==oh;r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=sha(S),compiled_in_this_run=source_pass is None,source_pass_record=source_pass['original_record']if source_pass else None)],module_object=dict(path=str(obj),sha256=oh),named_axiom_probes=12,callers=18,only_standard_axioms=True,warnings=sum(x['output'].count('warning:')for x in r['commands']))
except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
save();print(W/'verification.json')
