"""Portable guarded fresh actual register-return macro source/audit check.
Successful RegisterForward evidence supplies the exact twenty-nine project and five
external providers; no dependency is rebuilt or downloaded.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
p=argparse.ArgumentParser(description=__doc__)
for k in ('repo','dependency-root','forward-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
for k in ('source','audit','cache','lean'):p.add_argument('--'+k,type=Path)
p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
if not __debug__:p.error('Keep assertions enabled; do not use -O.')
R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
E=a.forward_evidence.resolve();e=json.loads(E.read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert e['status']=='PASS'and e['named_axiom_probes']==10 and e['callers']==12 and e['only_standard_axioms']is True and e['all_input_provider_postchecks']is True and e['all_fresh_objects_unchanged_after_audit']is True
assert e['source']['sha256']=='19c9310824d078818951ff5c79e0ed4d4263c9cedd7c5526473aa0782089b3e2'and e['audit']['sha256']=='765f7d093b7f605de831102c8b20a0a761bb29f0b4b320a166e7a3addfd733ac'
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('zero_helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
C,version=H.compiler_path(a.lean);assert sha(C)==e['compiler']['sha256']and version==e['compiler']['version']
libs,deps=H.dependency_libraries(D,a.library_path)
for n in ('Foundation','Mathlib'):assert deps[n]['pin']==e['dependencies'][n]['pin']and deps[n]['tracked_clean']is True and e['dependencies'][n]['tracked_clean']is True
assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticRegisterReturnPerm252.lean';A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_register_return_perm252_audit.lean'
assert a.source is not None or sha(S)=='79505169cf844ec85a4969219ba700340d76f6b6d54938b9a6a55a82cec84e9e'
assert a.audit is not None or sha(A)=='515ed1452ee7d7672a690c60d63e7c1d2341d9c69f0dc0c6fedad65e5ebb84fc'
module='BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252';prefix='SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252.'
expected_imports=['BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252'];assert H.lean_imports(S.read_text())==expected_imports and H.lean_imports(A.read_text())==[module]
def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
available={q['module']:dict(q,source=str(source(q['module'])))for q in e['reused_modules']}
fresh=e['fresh_modules'];assert len(fresh)==1 and fresh[0]['module']=='BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252'and fresh[0]['source_sha256']==e['source']['sha256'];q=fresh[0];available[q['module']]=dict(module=q['module'],source=str(source(q['module'])),source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256'])
if a.cache:
 for q in available.values():q['object']=str(a.cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
mods={};external=set()
def visit(m):
 if m in mods:return
 assert m in available;mods[m]=dict(available[m])
 for n in H.lean_imports(Path(mods[m]['source']).read_text()):
  if n in available:visit(n)
  else:assert n.startswith(('Foundation.','Mathlib.','Lean.'));external.add(n)
for m in expected_imports:
 if m in available:visit(m)
 else:external.add(m)
assert len(mods)==29
providers=[dict(q)for q in e['providers']]
for q in providers:
 rel=Path(q['module'].replace('.','/'));dep='Foundation'if q['module'].startswith('Foundation.')else'Mathlib';q['source']=str(Path(deps[dep]['path'])/rel.with_suffix('.lean'));obj=next(p/rel.with_suffix('.olean')for p in libs if(p/rel.with_suffix('.olean')).is_file());assert sha(q['source'])==q['source_sha256']and sha(obj)==q['object_sha256'];q['object']=str(obj.resolve());q['actual_first_provider']=True
assert len(providers)==5 and external-{x for x in external if x.startswith('Lean.')} <= {q['module']for q in providers}
cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(module.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for q in mods.values():
 assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256'];dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
actual=[]
for q in list(mods.values())+providers:
 assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256'];rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(x/rel for x in[cache,*libs]if(x/rel).is_file());assert sha(obj)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
tool=[];toolroot=C.parent.parent/'lib/lean'
for m in sorted({n for n in external if n.startswith('Lean.')}|{'Lean.Elab.Tactic.Omega'}):
 rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;obj=next(x/rel for x in[cache,*libs,toolroot]if(x/rel).is_file());assert reference.is_file()and sha(obj)==sha(reference),'Different first-selected toolchain object.'
 for prior in e.get('toolchain_providers',[]):
  if prior['module']==m:assert sha(obj)==prior['object_sha256']
 tool.append(dict(module=m,object=str(obj.resolve()),object_sha256=sha(obj),actual_first=str(obj),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference),actual_first_provider=True,scope='Actual first toolchain object equals sysroot reference; historical record hash compared whenever present.'))
expected_names=['step_left_row','step_left_recenter','left_transition_of_nat','step_left_numeral','return_block','return_dec','return_dec_probe','return_mark','return_mark_probe','return_inc','return_inc_probe'];names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);assert names==[prefix+n for n in expected_names]and len(re.findall(r'^example\b',A.read_text(),re.M))==12
inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,D/'lake-manifest.json']
for q in list(mods.values())+providers:inputs.extend([Path(q['source']),Path(q['object'])])
inputs.extend(Path(q[k])for q in tool for k in ('object','toolchain_reference'));inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,provider_evidence=dict(path=str(E),sha256=sha(E)),compiler=dict(path=str(C),version=version,sha256=sha(C)),source_overridden=a.source is not None,audit_overridden=a.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),providers=providers,toolchain_providers=tool,actual_first_providers=actual,exact_project_import_closure=True,dependencies=deps,before=before,commands=[],ordered_probe_names=names,expected_callers=12,LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(q):sha(q)for q in inputs};assert before==after
 for q in list(mods.values())+providers+tool:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next(x/rel for x in[cache,*libs,toolroot]if(x/rel).is_file());assert sha(first)==q['object_sha256']
  if q in tool:assert first.resolve()==Path(q['object']).resolve()
 _,da=H.dependency_libraries(D,a.library_path);assert deps==da;r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
def run(label,file,obj=None):
 cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,output=out));save();assert cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
try:
 obj=cache/Path(module.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=sha(obj);out=run('audit',aa)
 reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
 post();assert sha(obj)==oh;r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=sha(S))],module_object=dict(path=str(obj),sha256=oh),named_axiom_probes=11,callers=12,only_standard_axioms=True,warnings=sum(c['output'].count('warning:')for c in r['commands']))
except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
save();print(W/'verification.json')
