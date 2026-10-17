"""Guarded literal NIP nonfalsity comparison and cache-clear phase.
Checked represented Dispatch evidence supplies93 exact project prerequisites.
Only the new source/audit is checked; no dependency, site or bootstrap replay.
With --source-pass-evidence only the corrected audit is compiled; the exact
source PASS command and frozen object from the preserved failed run are reused.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
p=argparse.ArgumentParser(description=__doc__)
for k in ('repo','dependency-root','dispatch-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
for k in ('source','audit','cache','lean'):p.add_argument('--'+k,type=Path)
p.add_argument('--library-path',type=Path,action='append',default=[])
p.add_argument('--source-pass-evidence',type=Path)
p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';s=importlib.util.spec_from_file_location('zero_spare_helpers',helper);H=importlib.util.module_from_spec(s);s.loader.exec_module(H)
records=[(a.dispatch_evidence.resolve(),14,18,'3cffa709f7d982775de6be2cc2b04f786937867365943a95d9a3e629ca7af7a2','290a3446eaeba0c3fbc3f6d946eaeb7371f9fedbd3570bdc825e169a1201fd5e','dccf09186d1b7f8d5423af675b0b355a83f46d04761b81a81cfef747ed7584d7')]
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
assert len(mods)==93 and set(providers)=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Arithmetic.Exponential.Exp','Foundation.FirstOrder.Arithmetic.Definability.Absoluteness'}
for m,q in providers.items():
 rel=Path(m.replace('.','/'));dep='Foundation'if m.startswith('Foundation.')else'Mathlib';q['source']=str(Path(deps[dep]['path'])/rel.with_suffix('.lean'));obj=next(p/rel.with_suffix('.olean')for p in libs if(p/rel.with_suffix('.olean')).is_file());assert sha(q['source'])==q['source_sha256']and sha(obj)==q['object_sha256'];q['object']=str(obj.resolve());q['actual_first_provider']=True
S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticControlNip254.lean'
A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_control_nip254_audit.lean'
assert a.source is not None or sha(S)=='68fa14b137b5f1a2fbf1212f15177a833a08fdd5a846f96850dd9e34962035a4'
assert a.audit is not None or sha(A)=='d5c774587acef0f241639ad5890dbfad0863832b5abdb1dba3bf7c98bc7bc295'
module='BusyBeaver.ZFC.ArithmeticControlNip254';prefix='SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.'
imports=['BusyBeaver.ZFC.ArithmeticControlDispatch254'];assert H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[module]
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
names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);expected=['cacheZeroS1_source', 'cacheZeroInc_source', 'cacheClearTest_source', 'cacheClearAgain_source', 'cacheClearExit_source', 'stackPopEntry_source', 'next_cache_zero_inc', 'cache_clear_repeat', 'nip_prepare', 'clear_cache', 'nip_cache_zero', 'nip_cache_positive', 'nip_nonfalsity', 'dispatch_nip_nonfalsity'];assert names==[prefix+n for n in expected]and len(re.findall(r'^example\b',A.read_text(),re.M))==18
source_pass=None
if a.source_pass_evidence:
 E=a.source_pass_evidence.resolve();assert sha(E)=='a06fc6beb1dbf7c2e2ba589456ed16b2ff5eed71976a59492e99188f1dda0255'
 e=json.loads(E.read_text());assert e['status']=='FAIL'and len(e['commands'])==2
 sc,ac=e['commands'];assert sc['label']=='source'and sc['exit_code']==0 and ac['label']=='audit'and ac['exit_code']!=0
 assert e['source']['sha256']==sha(S)=='68fa14b137b5f1a2fbf1212f15177a833a08fdd5a846f96850dd9e34962035a4'and e['audit']['sha256']=='fa3b993edc950ac36293a0b907525bbc2430bebbece696128cff5d59ac096f21'
 assert e['compiler']['sha256']==sha(C)and e['compiler']['version']==version
 assert sc['command'][0]==e['compiler']['path']and'-M4096'in sc['command']and sc['command'][-1]==e['source']['snapshot']
 ps=Path(e['source']['snapshot']);pa=Path(e['audit']['snapshot']);assert sha(ps)==e['source']['sha256']and sha(pa)==e['audit']['sha256']
 pg=E.parent/'executed-check.py';assert sha(pg)=='e951cab6b1b638d8784f2bcd207cd6f32f07472e230bc2e4686970293dfbe67e'and e['before'][str('/tmp/zfc-arithmetic-control-nip/check.py')]==sha(pg)
 for q in e['reused_modules']:
  z=mods[q['module']];assert z['source_sha256']==q['source_sha256']and z['object_sha256']==q['object_sha256']
 assert len(e['reused_modules'])==len(mods)
 for q in e['providers']:
  z=providers[q['module']];assert z['source_sha256']==q['source_sha256']and z['object_sha256']==q['object_sha256']
 for n in ('Foundation','Mathlib'):assert e['dependencies'][n]['pin']==deps[n]['pin']
 assert e['dependencies']['lake_manifest_sha256']==deps['lake_manifest_sha256']
 for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
 so=Path(sc['command'][sc['command'].index('-o')+1]);so=(a.cache.resolve()/Path(module.replace('.','/')).with_suffix('.olean'))if a.cache else so
 assert sha(so)=='eb4cc80dd3c417695494536c1ce83d3f1459c08260f0b203942110e11ebdaeaa'
 source_pass=dict(original_record=dict(path=str(E),sha256=sha(E),status=e['status']),source_pass_command=sc,overall_failed_audit_command=ac,source_snapshot=dict(path=str(ps),sha256=sha(ps)),failed_audit_snapshot=dict(path=str(pa),sha256=sha(pa)),original_executed_guard=dict(path=str(pg),sha256=sha(pg)),object=dict(path=str(so.resolve()),sha256=sha(so)),object_hash_scope='Frozen current object of the recorded successful source command. The original failed overall record did not persist its local before-audit object hash; no retrospective hash attestation is inferred.',source_compilations_in_this_run=0)
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
r.update(reused_prior_source_pass=source_pass is not None,prior_source_pass=source_pass,source_compilations=0 if source_pass or a.prepare_only else 1)
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
 cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,output=out));save();assert cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
try:
 obj=cache/Path(module.replace('.','/')).with_suffix('.olean')
 if not source_pass:run('source',ss,obj)
 oh=sha(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports);post();assert sha(obj)==oh;r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=sha(S),compiled_in_this_run=source_pass is None,source_pass_record=source_pass['original_record']if source_pass else None)],module_object=dict(path=str(obj),sha256=oh),named_axiom_probes=14,callers=18,only_standard_axioms=True,warnings=sum(x['output'].count('warning:')for x in r['commands']))
except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
save();print(W/'verification.json')
