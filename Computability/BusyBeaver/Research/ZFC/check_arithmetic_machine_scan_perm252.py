"""Portable guarded fresh actual frozen252 unbounded scan source and audit check.
Existing exact recorded project/dependency objects are reused, never rebuilt.
Prepare-only verifies provenance and snapshots without running a Lean proof build.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time

MODE = 'scan'
MODULE = 'BusyBeaver.ZFC.ArithmeticMachineScanPerm252'
SOURCE_SHA = '65078ee1558e96cdfc160877551fd91861ad1903caf06331686c798f028d1229'
AUDIT_SHA = '05638001f9963bbe907a83257ea85a344a9943fbf5800ea06e159854334ed9aa'
AUDIT_NAME = 'arithmetic_machine_scan_perm252_audit.lean'
NAMES = ['odd_mod_two', 'odd_div_two', 'apply_right_one', 'seekInc_action', 'scanFrame_defined', 'seekInc_step', 'seekInc_scan', 'seekInc_scan_graph']
CALLERS = 11

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ('repo','dependency-root','prefix-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
 if MODE=='scan':p.add_argument('--run-from-evidence',type=Path,required=True)
 for k in ('cache','source','audit','lean'):p.add_argument('--'+k,type=Path)
 if MODE=='scan':
  for k in ('run-from-cache','prefix-cache'):p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve()
 assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Output must be fresh and outside repository/dependency trees.'
 W.mkdir(parents=True,exist_ok=True);sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('prefix_scan_helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 F=a.prefix_evidence.resolve();f=json.loads(F.read_text());records=[(F,f)]
 if MODE=='scan':E=a.run_from_evidence.resolve();e=json.loads(E.read_text());records.insert(0,(E,e))
 def validate(d,probes,callers,source_hash,audit_hash):
  assert d['status']=='PASS'and d['named_axiom_probes']==probes and d['callers']==callers
  assert d['only_standard_axioms']is True and d['all_input_provider_postchecks']is True and d['all_fresh_objects_unchanged_after_audit']is True
  assert d['source']['sha256']==source_hash and d['audit']['sha256']==audit_hash
 validate(f,10,10,'396b573e4e94058859608ffa74be668f1d29a092f4853bdeafc0702da222cd55','08ea04e7d7f3705e7ef8a69873f0cf9f38bd7bb1fb1051b6c9125a6ef2bc9c6c')
 if MODE=='scan':validate(e,19,20,'074395bea5c0762a808022dc2b2d9cd18cf6bd0f69a36e3fe3d73f6e7c8277eb','d6ea489e770e8668c8a57f6c15448dcd4151f2e643552a338ecb559e28b84cf5')
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 for _,d in records:
  assert sha(C)==d['compiler']['sha256']and version==d['compiler']['version']
  for n in ('Foundation','Mathlib'):assert deps[n]['pin']==d['dependencies'][n]['pin']and deps[n]['tracked_clean']is True and d['dependencies'][n]['tracked_clean']is True
  assert deps['lake_manifest_sha256']==d['dependencies']['lake_manifest_sha256']
  for n,q in deps['providers'].items():assert q['sha256']==d['dependencies']['providers'][n]['sha256']
 def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
 mods={};providers={}
 def add(q):
  m=q['module'];q=dict(q,source=str(source(m)))
  if m in mods:assert q['source_sha256']==mods[m]['source_sha256']and q['object_sha256']==mods[m]['object_sha256'],'Same source but different selected project objects need separate explicit evidence.'
  else:mods[m]=q
 for _,d in records:
  for q in d['reused_modules']:add(q)
  for q in d['providers']:
   if q['module']in providers:assert q['source_sha256']==providers[q['module']]['source_sha256']and q['object_sha256']==providers[q['module']]['object_sha256']
   else:providers[q['module']]=dict(q)
  if MODE=='scan':
   fresh=d['fresh_modules'];assert len(fresh)==1
   q=fresh[0];assert q['source_sha256']==d['source']['sha256'];add(dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256']))
 assert len(mods)==(26 if MODE=='scan'else 11)and len(providers)==(5 if MODE=='scan'else 3)
 if a.cache:
  for q in mods.values():q['object']=str(a.cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
 if MODE=='scan':
  for cache,m in [(a.run_from_cache,'BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252'),(a.prefix_cache,'BusyBeaver.ZFC.ArithmeticTapePrefix254')]:
   if cache:mods[m]['object']=str(cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))
 for q in mods.values():assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256']
 for m,q in providers.items():
  rel=Path(m.replace('.','/'));dep='Foundation'if m.startswith('Foundation.')else'Mathlib';q['source']=str(Path(deps[dep]['path'])/rel.with_suffix('.lean'));obj=next(p/rel.with_suffix('.olean')for p in libs if(p/rel.with_suffix('.olean')).is_file())
  assert sha(q['source'])==q['source_sha256']and sha(obj)==q['object_sha256'];q['object']=str(obj.resolve());q['actual_first_provider']=True
 S=a.source.resolve()if a.source else source(MODULE);A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC'/AUDIT_NAME
 assert a.source is not None or sha(S)==SOURCE_SHA;assert a.audit is not None or sha(A)==AUDIT_SHA
 expected_imports=['BusyBeaver.ZFC.ArithmeticTapePrefix254','BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252']if MODE=='scan'else['BusyBeaver.ZFC.ArithmeticCantor','Foundation.FirstOrder.Arithmetic.Exponential.Exp']
 assert H.lean_imports(S.read_text())==expected_imports and H.lean_imports(A.read_text())==[MODULE]
 prefix='SetTheory.BusyBeaver.ZFC.'+MODULE.rsplit('.',1)[-1]+'.';names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)
 assert names==[prefix+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==CALLERS
 seen=set();external=set();visiting=set()
 def visit(m):
  if m in seen:return
  assert m in mods and m not in visiting;visiting.add(m)
  for n in H.lean_imports(Path(mods[m]['source']).read_text()):
   if n in mods:visit(n)
   else:assert n.startswith(('Foundation.','Mathlib.','Lean.'));external.add(n)
  visiting.remove(m);seen.add(m)
 for m in expected_imports:
  if m in mods:visit(m)
  else:external.add(m)
 assert seen==set(mods)
 assert external-{q for q in external if q.startswith('Lean.')} <= set(providers)
 cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual=[]
 for q in list(mods.values())+list(providers.values()):
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(x/rel for x in[cache,*libs]if(x/rel).is_file());assert sha(obj)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
 toolroot=C.parent.parent/'lib/lean';tool=[]
 for m in sorted({q for q in external if q.startswith('Lean.')}|{'Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;obj=next(x/rel for x in[cache,*libs,toolroot]if(x/rel).is_file());assert reference.is_file()and sha(obj)==sha(reference),'Different first-selected toolchain object.'
  for _,d in records:
   for prior in d.get('toolchain_providers',[]):
    if prior['module']==m:assert sha(obj)==prior['object_sha256']
  tool.append(dict(module=m,object=str(obj.resolve()),object_sha256=sha(obj),actual_first=str(obj),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference),actual_first_provider=True,scope='First-selected object equals toolchain reference; checked historically when an input record identifies this provider.'))
 inputs=[Path(__file__).resolve(),helper,*[p for p,_ in records],C,S,A,ss,aa,D/'lake-manifest.json']
 for q in list(mods.values())+list(providers.values()):inputs.extend([Path(q['source']),Path(q['object'])])
 inputs.extend(Path(q[k])for q in tool for k in ('object','toolchain_reference'));inputs=list(dict.fromkeys(p.resolve()for p in inputs));before={str(p):sha(p)for p in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,compiler=dict(path=str(C),version=version,sha256=sha(C)),provider_evidence=[dict(path=str(p),sha256=sha(p))for p,_ in records],source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),reused_count=len(mods),providers=list(providers.values()),actual_first_providers=actual,toolchain_providers=tool,exact_project_import_closure=True,dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,ordered_probe_names=names,expected_callers=CALLERS)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(p):sha(p)for p in inputs};assert before==after
  for q in list(mods.values())+list(providers.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(x/rel for x in[cache,*libs,toolroot]if(x/rel).is_file());assert sha(obj)==q['object_sha256']
   if q in tool:assert str(obj.resolve())==q['object']
  _,da=H.dependency_libraries(D,a.library_path);assert deps==da;r.update(after=after,all_input_provider_postchecks=True)
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,output=out));save();assert cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=sha(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  assert[n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
  post();assert sha(obj)==oh;r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,module_object=dict(path=str(obj),sha256=oh),fresh_modules=[dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S))],named_axiom_probes=len(NAMES),callers=CALLERS,only_standard_axioms=True,warnings=sum(c['output'].count('warning:')for c in r['commands']))
 except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()
