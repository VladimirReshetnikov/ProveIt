"""Bounded guarded checker for the explicit all-internal fixed block substrate.

Only the supplied reviewed BlockExecution source and audit are freshly checked.
Explicit successful Pi1-framework and append-execution records supply the
34 project providers. Cached external dependencies are reused; no build/fetch.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,tempfile,time

MODULE='BusyBeaver.ZFC.ArithmeticCommandBlockExecution254'
SOURCE=Path('Computability/BusyBeaver/Lean')/Path(MODULE.replace('.','/')).with_suffix('.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_block_execution254_audit.lean')
SOURCE_HASH='b96fe20537520d345c437df816a389a2cb899b86e050ede16b0bf0507926754a'
AUDIT_HASH='c7b7871878b758974a2c45e272e0f418747ebe8b67d110db9a6d2cbe88ebb6fd'
PROBES=['SetTheory.'+MODULE+'.'+n for n in ('eval_mp','eval_drop','eval_nip','eval_ax','eval_append_halt','eval_append_success','eval_nips','wim_ne_one','wal_ne_one','wim_one_ne_zero','gate_ne_one','axList_ne_one','circuit_consMp','circuit_consDrop','circuit_consNip','circuit_consAx','circuit_nips','eval_discard','discard_contract')]
EXTERNAL={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
def project_source(repo,mod):
 if mod=='FirstOrder.Fol':return repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
 assert mod.startswith('BusyBeaver.ZFC.')
 return repo/'Computability/BusyBeaver/Lean'/Path(mod.replace('.','/')).with_suffix('.lean')
def normalize_providers(record):
 values=record['providers']
 if isinstance(values,dict):return {m:dict(module=m,source=q.get('source'),source_sha256=q.get('source_sha256'),object=q['path'],object_sha256=q['sha256'])for m,q in values.items()}
 assert len(values)==len({q['module']for q in values})
 return {q['module']:dict(q)for q in values}
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ('repo','dependency-root','framework-evidence','execution-evidence'):p.add_argument('--'+key,type=Path,required=True)
 for key in ('source','audit','output','framework-cache','execution-cache','lean'):p.add_argument('--'+key,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 R=a.repo.resolve();root=a.dependency_root.resolve();W=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-block-execution-'));assert not W.is_relative_to(R)and not W.is_relative_to(root)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('block_cantor_helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest();F=a.framework_evidence.resolve();E=a.execution_evidence.resolve();f,e=[json.loads(q.read_text())for q in(F,E)]
 assert f['status']==e['status']=='PASS'and f['named_axiom_probes']==6 and f['callers']==8 and e['named_axiom_probes']==15 and e['callers']==20 and f['only_standard_axioms']is True and e['only_standard_axioms']is True
 assert f['all_input_provider_postchecks']is True and e['all_sources_objects_providers_unchanged']is True
 C,version=H.compiler_path(a.lean or Path(f['compiler']['path']));assert sha(C)==f['compiler']['sha256']==e['compiler']['sha256'];assert 'version 4.32.0,'in version
 libs,deps=H.dependency_libraries(root,a.library_path)
 for base in (f,e):
  for name in ('Foundation','Mathlib'):
   assert deps[name]['pin']==base['dependencies'][name]['pin'] and deps[name]['tracked_clean'] is True and base['dependencies'][name]['tracked_clean'] is True
  assert deps['lake_manifest_sha256']==base['dependencies']['lake_manifest_sha256']
  assert set(deps['providers'])==set(base['dependencies']['providers'])
  for name,q in deps['providers'].items():assert q['sha256']==base['dependencies']['providers'][name]['sha256']
 assert version==f['compiler']['version']==e['compiler']['version']
 mods={};alts=[]
 def add(q,cache):
  q=dict(q,source=str(project_source(R,q['module'])))
  if cache:q['object']=str(cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
  assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256']
  if q['module']in mods:
   assert mods[q['module']]['source_sha256']==q['source_sha256']
   if mods[q['module']]['object_sha256']!=q['object_sha256']:
    assert q['module']=='BusyBeaver.ZFC.ArithmeticCantor';alts.append(q)
  else:mods[q['module']]=q
 for q in f['reused_modules']:add(q,a.framework_cache)
 add(dict(module='BusyBeaver.ZFC.ArithmeticProofWordContract254',source=f['source']['path'],source_sha256=f['source']['sha256'],object=f['module_object']['path'],object_sha256=f['module_object']['sha256']),a.framework_cache)
 for q in e['reused_modules']:add(q,a.execution_cache)
 add(dict(module='BusyBeaver.ZFC.ArithmeticCommandExecution254',source=e['source']['path'],source_sha256=e['source']['sha256'],object=e['module_object']['path'],object_sha256=e['module_object']['sha256']),a.execution_cache)
 assert len(mods)==34
 providers=[]
 fp,ep=normalize_providers(f),normalize_providers(e)
 assert set(fp)==set(ep)==EXTERNAL
 for name,q in fp.items():
  rel=Path(name.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation'if name.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean')
  assert obj and src.is_file()
  for old in(q,ep[name]):
   assert sha(obj)==old['object_sha256']
   if old.get('source_sha256'):assert sha(src)==old['source_sha256']
  providers.append(dict(module=name,source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True))
 S=a.source.resolve()if a.source else R/SOURCE;A=a.audit.resolve()if a.audit else R/AUDIT;module=MODULE
 assert a.source is not None or sha(S)==SOURCE_HASH
 assert a.audit is not None or sha(A)==AUDIT_HASH
 assert H.lean_imports(S.read_text())==['BusyBeaver.ZFC.ArithmeticCommandExecution254','BusyBeaver.ZFC.ArithmeticProofWordContract254'];assert H.lean_imports(A.read_text())==[module]
 required={};external=set();visiting=set()
 def visit(mod):
  if mod in required:return
  assert mod not in visiting and mod in mods;visiting.add(mod);q=mods[mod]
  for imported in H.lean_imports(Path(q['source']).read_text()):
   if imported in mods:visit(imported)
   else:assert imported.startswith(('Foundation.','Mathlib.'));external.add(imported)
  visiting.remove(mod);required[mod]=q
 for mod in H.lean_imports(S.read_text()):visit(mod)
 assert set(required)==set(mods),'Unexpected extra or missing project closure.'
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);assert names==PROBES;assert len(re.findall(r'^example\b',A.read_text(),re.M))==20
 cache=W/'cache';cache.mkdir();snap=W/'sources';local=snap/'BusyBeaver/ZFC';local.mkdir(parents=True)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual_project_providers=[]
 for q in mods.values():
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next((x/rel for x in [cache,*libs] if(x/rel).is_file()),None)
  assert first and sha(first)==q['object_sha256']
  actual_project_providers.append(dict(module=q['module'],actual_first=str(first),resolved=str(first.resolve()),sha256=sha(first)))
 direct_external_providers=[]
 assert external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'}
 for mod in sorted(external):
  rel=Path(mod.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation' if mod.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean');assert obj and src.is_file()
  direct_external_providers.append(dict(module=mod,source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True))
 ss=local/'ArithmeticCommandBlockExecution254.lean';aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 inputs=[Path(__file__).resolve(),helper,F,E,C,S,A,ss,aa,root/'lake-manifest.json']
 for q in list(mods.values())+alts+providers+direct_external_providers:inputs.extend([Path(q['source']),Path(q['object'])])
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,compiler=dict(f['compiler'],path=str(C),version=version),framework_evidence=dict(path=str(F),sha256=sha(F)),execution_evidence=dict(path=str(E),sha256=sha(E)),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),same_source_object_alternatives=alts,providers=providers,actual_project_providers=actual_project_providers,direct_external_providers=direct_external_providers,exact_project_import_closure=True,dependencies_match_both_baselines=True,reused_count=len(mods),source_override=a.source is not None,audit_override=a.audit is not None,dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 save()
 def postchecks():
  after={str(q):sha(q)for q in inputs};assert before==after
  for q in mods.values():
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next((x/rel for x in[cache,*libs]if(x/rel).is_file()),None)
   assert actual and actual.resolve()==Path(q['object']).resolve()and sha(actual)==q['object_sha256']
  for q in providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next((x/rel for x in libs if(x/rel).is_file()),None)
   assert actual and actual.resolve()==Path(q['object']).resolve()and sha(actual)==q['object_sha256']
  _,depafter=H.dependency_libraries(root,a.library_path);assert deps==depafter
  d.update(after=after,all_input_provider_postchecks=True)
 if a.prepare_only:postchecks();save();print(W/'verification.json');return
 def run(label,q,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(q)];t=time.monotonic();r=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;(W/(label+'.log')).write_text(out);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=out));save();assert r.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/'BusyBeaver/ZFC/ArithmeticCommandBlockExecution254.olean';run('source',ss,obj);oh=sha(obj);d['object_immediately_after_source']=dict(path=str(obj),sha256=oh);save();out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names;assert all(set(x.strip()for x in v.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,v in reports)
  postchecks();assert sha(obj)==oh
  d.update(status='PASS',all_input_provider_postchecks=True,module_object=dict(path=str(obj),sha256=oh),named_axiom_probes=len(names),callers=20,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except Exception as ex:d.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()
