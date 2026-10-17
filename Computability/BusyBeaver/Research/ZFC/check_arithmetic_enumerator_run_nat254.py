"""Check only the all-Nat adapter for the literal Enum254 scheduler.

Successful EnumeratorRun evidence supplies 27 exact imported project objects.
No arithmetic prerequisites or external dependencies are rebuilt or fetched.
Inherited unused object alternatives are historical metadata, not providers.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, tempfile, time

MODULE='BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254'
PREREQUISITE='BusyBeaver.ZFC.ArithmeticEnumeratorRun254'
SOURCE_SHA='9a43f17d33e0225ed70682980978dfb992321d621c0aba3960d980c2f414991b'
AUDIT_SHA='d41fb90fbaab94dd95ec4c733d78641e35173cbf6eae72a4b96d731a1797c7b2'
RUN_SHA='22848676b37e9094d18744f706d8726278d368cd52c8d52391dfa291f650d397'
PROBES=['encodeSt_ne_zero','encodeResult_eq_zero','run_succ_first','run_encode_nat',
 'runDef_encode_nat','run_zero_iff_native_none','haltsFrom_of_run_none',
 'run_none_of_haltsFrom','halts_iff_native','encodeSt_s0','blank_halts_iff']
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.'

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ('repo','dependency-root','run-evidence'):p.add_argument('--'+k,type=Path,required=True)
 for k in ('run-cache','source','audit','output','lean'):p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use Python -O.')
 R=a.repo.resolve();root=a.dependency_root.resolve()
 W=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-enumerator-run-nat-'))
 assert not W.is_relative_to(R)and not W.is_relative_to(root),'Use scratch output outside both repositories.'
 assert not W.exists()or(W.is_dir()and not any(W.iterdir())),'Output must be new or empty.'
 W.mkdir(parents=True,exist_ok=True)
 sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 sp=importlib.util.spec_from_file_location('enum_nat_cantor_helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 E=a.run_evidence.resolve();e=json.loads(E.read_text())
 assert e['status']=='PASS'and e['named_axiom_probes']==16 and e['callers']==13
 assert e['only_standard_axioms']is True and e['all_input_provider_postchecks']is True
 assert e['source']['sha256']==RUN_SHA
 C,version=H.compiler_path(a.lean);assert sha(C)==e['compiler']['sha256']and version==e['compiler']['version']
 libs,deps=H.dependency_libraries(root,a.library_path)
 for name in ('Foundation','Mathlib'):
  assert deps[name]['pin']==e['dependencies'][name]['pin']
  assert deps[name]['tracked_clean']is True and e['dependencies'][name]['tracked_clean']is True
 assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
 assert set(deps['providers'])==set(e['dependencies']['providers'])
 for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
 def mapped_source(m):
  rel=Path(m.replace('.','/')).with_suffix('.lean')
  if m=='FirstOrder.Fol':return R/'Logic/FirstOrder/Lean'/rel
  assert m.startswith('BusyBeaver.ZFC.');return R/'Computability/BusyBeaver/Lean'/rel
 mods={}
 def add(q):
  q=dict(q);m=q['module'];assert m not in mods
  q['source']=str(mapped_source(m))
  if a.run_cache:q['object']=str(a.run_cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))
  assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256'];mods[m]=q
 for q in e['reused_modules']:add(q)
 fresh=e.get('module_object')
 if fresh is None:
  fs=e['fresh_modules'];assert len(fs)==1 and fs[0]['module']==PREREQUISITE and fs[0]['source_sha256']==RUN_SHA;fresh=fs[0]
 add(dict(module=PREREQUISITE,source=e['source']['path'],source_sha256=RUN_SHA,object=fresh['path'],object_sha256=fresh['sha256']))
 assert len(mods)==27
 expected_external={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
 assert isinstance(e['providers'],list)and {q['module']for q in e['providers']}==expected_external
 providers=[]
 for q in e['providers']:
  rel=Path(q['module'].replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation'if q['module'].startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean')
  assert obj and sha(obj)==q['object_sha256']and sha(src)==q['source_sha256']
  providers.append(dict(module=q['module'],source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True))
 S=a.source.resolve()if a.source else mapped_source(MODULE)
 A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_enumerator_run_nat254_audit.lean'
 assert a.source is not None or sha(S)==SOURCE_SHA
 assert a.audit is not None or sha(A)==AUDIT_SHA
 assert H.lean_imports(S.read_text())==[PREREQUISITE]and H.lean_imports(A.read_text())==[MODULE]
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)
 assert names==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==14
 required=set();external=set()
 def visit(m):
  if m in required:return
  assert m in mods;required.add(m)
  for n in H.lean_imports(Path(mods[m]['source']).read_text()):
   if n in mods:visit(n)
   else:assert n.startswith(('Foundation.','Mathlib.'));external.add(n)
 visit(PREREQUISITE);assert required==set(mods)
 cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean'
 shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual=[]
 for q in list(mods.values())+providers:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(x/rel for x in[cache,*libs]if(x/rel).is_file());assert sha(obj)==q['object_sha256']
  actual.append(dict(module=q['module'],actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
 inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,root/'lake-manifest.json']
 for q in list(mods.values())+providers:inputs.extend((Path(q['source']),Path(q['object'])))
 inputs.extend(Path(q['path'])for q in deps['providers'].values())
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,source_overridden=a.source is not None,audit_overridden=a.audit is not None,compiler=dict(path=str(C),version=version,sha256=sha(C)),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),run_evidence=dict(path=str(E),sha256=sha(E)),reused_modules=list(mods.values()),inherited_unused_object_alternatives=e.get('same_source_object_alternatives',[]),unused_alternative_scope='Historical prerequisite metadata only; not selected, relocated, or rechecked as providers.',providers=providers,actual_first_providers=actual,exact_project_import_closure=True,dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def postcheck():
  after={str(q):sha(q)for q in inputs};assert after==before
  for q in list(mods.values())+providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next(x/rel for x in[cache,*libs]if(x/rel).is_file());assert sha(first)==q['object_sha256']
  _,depa=H.dependency_libraries(root,a.library_path);assert deps==depa
  return after
 save()
 if a.prepare_only:r.update(after=postcheck(),all_input_provider_postchecks=True);save();print(W/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();p=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=p.stdout+p.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=p.returncode,output=out));save()
  assert p.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out
  print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=sha(obj);out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  assert[n for n,_ in reports]==names
  assert all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
  after=postcheck();assert sha(obj)==oh
  r.update(status='PASS',after=after,all_input_provider_postchecks=True,all_fresh_objects_unchanged_after_audit=True,module_object=dict(path=str(obj),sha256=oh),fresh_modules=[dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S))],named_axiom_probes=11,callers=14,only_standard_axioms=True,warnings=sum(c['output'].count('warning:')for c in r['commands']))
 except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()
