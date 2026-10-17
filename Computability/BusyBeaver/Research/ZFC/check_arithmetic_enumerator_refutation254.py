"""Bounded guarded checker for the internal accepted-validator to scheduler-halting direction.

Only the supplied reviewed EnumeratorRefutation source and audit are freshly checked.
Explicit successful scheduler-run and refutation-word records supply the
41 project providers. Cached external dependencies are reused; no build/fetch.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,tempfile,time

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ('repo','dependency-root','run-evidence','refutation-evidence'):p.add_argument('--'+key,type=Path,required=True)
 p.add_argument('--run-cache',type=Path);p.add_argument('--refutation-cache',type=Path)
 p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path);p.add_argument('--output',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 R=a.repo.resolve();root=a.dependency_root.resolve();W=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-enumerator-refutation-check-'));assert not W.is_relative_to(R)and not W.is_relative_to(root)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('block_cantor_helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest();F=a.run_evidence.resolve();E=a.refutation_evidence.resolve();f,e=[json.loads(q.read_text())for q in(F,E)]
 assert f['status']==e['status']=='PASS'and f['named_axiom_probes']==16 and f['callers']==13 and e['named_axiom_probes']==11 and e['callers']==12 and f['only_standard_axioms']is True and e['only_standard_axioms']is True
 assert f['all_input_provider_postchecks']is True and (e.get('all_sources_objects_providers_unchanged')is True or e.get('all_input_provider_postchecks')is True)
 probe_count=5;caller_count=9
 C,version=H.compiler_path(a.lean);assert sha(C)==f['compiler']['sha256']==e['compiler']['sha256'];assert version==f['compiler']['version']==e['compiler']['version']
 libs,deps=H.dependency_libraries(root,a.library_path)
 for base in (f,e):
  for name in ('Foundation','Mathlib'):
   assert deps[name]['pin']==base['dependencies'][name]['pin'] and deps[name]['tracked_clean'] is True and base['dependencies'][name]['tracked_clean'] is True
  assert deps['lake_manifest_sha256']==base['dependencies']['lake_manifest_sha256']
  assert set(deps['providers'])==set(base['dependencies']['providers'])
  for name,q in deps['providers'].items():assert q['sha256']==base['dependencies']['providers'][name]['sha256']
 assert subprocess.check_output([str(C),'--version'],text=True).strip()==f['compiler']['version']==e['compiler']['version']
 mods={};alts=[]
 def add(q,relocated=None):
  q=dict(q);m=q['module'];rel=Path(m.replace('.','/')).with_suffix('.lean')
  if m=='FirstOrder.Fol':q['source']=str(R/'Logic/FirstOrder/Lean'/rel)
  else:assert m.startswith('BusyBeaver.ZFC.');q['source']=str(R/'Computability/BusyBeaver/Lean'/rel)
  if relocated:q['object']=str(relocated.resolve()/rel.with_suffix('.olean'))
  assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256']
  if q['module']in mods:
   assert mods[q['module']]['source_sha256']==q['source_sha256']
   if mods[q['module']]['object_sha256']!=q['object_sha256']:
    assert q['module']=='BusyBeaver.ZFC.ArithmeticCantor';q['used_as_provider']=False;alts.append(q)
  else:mods[q['module']]=q
 for q in f['reused_modules']:add(q,a.run_cache)
 fresh=f['module_object']
 add(dict(module='BusyBeaver.ZFC.ArithmeticEnumeratorRun254',source=f['source']['path'],source_sha256=f['source']['sha256'],object=fresh['path'],object_sha256=fresh['sha256']),a.run_cache)
 for q in e['reused_modules']:add(q,a.refutation_cache)
 fresh=e['fresh_modules'][0];assert fresh['module']=='BusyBeaver.ZFC.ArithmeticRefutationWord254' and fresh['source_sha256']==e['source']['sha256']
 add(dict(module=fresh['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],object=fresh['path'],object_sha256=fresh['sha256']),a.refutation_cache)
 assert len(mods)==41
 providers=[]
 expected_external={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
 previous_execution=e['providers']if isinstance(e['providers'],dict)else{q['module']:dict(path=q['object'],sha256=q['object_sha256'],source_sha256=q['source_sha256'])for q in e['providers']}
 assert {q['module'] for q in f['providers']}==set(previous_execution)==expected_external
 for q in f['providers']:
  rel=Path(q['module'].replace('.','/'));obj=next((x/rel.with_suffix('.olean') for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation' if q['module'].startswith('Foundation.') else 'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean')
  assert obj and src.is_file() and sha(obj)==q['object_sha256'] and sha(src)==q['source_sha256']
  providers.append(dict(module=q['module'],source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True))
 for name,q in previous_execution.items():
  old=next(x for x in providers if x['module']==name);assert old['object_sha256']==q['sha256']
  if 'source_sha256'in q:assert old['source_sha256']==q['source_sha256']
 S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticEnumeratorRefutation254.lean'
 A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_enumerator_refutation254_audit.lean'
 assert a.source is not None or sha(S)=='c6c43b2d226124aafb5aa303e4e5e780cb5e83703199ee52adfb1736824f3509'
 assert a.audit is not None or sha(A)=='fb4a56199aacef2bc1629e563cf4c363c77028a3c2d3b434fe068ebcfec62ec4'
 module='BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254';prefix='SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254.'
 assert H.lean_imports(S.read_text())==['BusyBeaver.ZFC.ArithmeticEnumeratorRun254','BusyBeaver.ZFC.ArithmeticRefutationWord254'];assert H.lean_imports(A.read_text())==[module]
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
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);assert names==[prefix+n for n in ('halts_of_accepted','represented_halt','forwardSentence_true','isigma1_proves_forward','peano_proves_forward')];assert len(names)==probe_count and len(re.findall(r'^example\b',A.read_text(),re.M))==caller_count
 cache=W/'cache';cache.mkdir();snap=W/'sources';local=snap/'BusyBeaver/ZFC';local.mkdir(parents=True)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual_project_providers=[]
 for q in mods.values():
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next((x/rel for x in [cache,*libs] if(x/rel).is_file()),None)
  assert first and sha(first)==q['object_sha256']
  actual_project_providers.append(dict(module=q['module'],actual_first=str(first),resolved=str(first.resolve()),sha256=sha(first)))
 direct_external_providers=[]
 for mod in sorted(external):
  rel=Path(mod.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation' if mod.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean');assert obj and src.is_file()
  direct_external_providers.append(dict(module=mod,source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True))
 ss=local/'ArithmeticEnumeratorRefutation254.lean';aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 inputs=[Path(__file__).resolve(),helper,F,E,C,S,A,ss,aa,root/'lake-manifest.json']
 for q in list(mods.values())+alts+providers+direct_external_providers:inputs.extend([Path(q['source']),Path(q['object'])])
 inputs.extend(Path(q['path'])for q in deps['providers'].values())
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,reused_count=len(mods),compiler=dict(path=str(C),version=version,sha256=sha(C)),run_evidence=dict(path=str(F),sha256=sha(F)),refutation_evidence=dict(path=str(E),sha256=sha(E)),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),same_source_object_alternatives=alts,providers=providers,actual_project_providers=actual_project_providers,direct_external_providers=direct_external_providers,exact_project_import_closure=True,dependencies_match_both_baselines=True,dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 save()
 if a.prepare_only:
  after={str(q):sha(q)for q in inputs};assert before==after
  for q in mods.values():assert sha(cache/Path(q['module'].replace('.','/')).with_suffix('.olean'))==q['object_sha256']
  _,depafter=H.dependency_libraries(root,a.library_path);assert deps==depafter
  d.update(after=after,all_input_provider_postchecks=True,all_fresh_objects_unchanged_after_audit=True);save();print(W/'verification.json');return
 def run(label,q,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(q)];t=time.monotonic();r=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;(W/(label+'.log')).write_text(out);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=out));save();assert r.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/'BusyBeaver/ZFC/ArithmeticEnumeratorRefutation254.olean';run('source',ss,obj);oh=sha(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names;assert all(set(x.strip()for x in v.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,v in reports)
  after={str(q):sha(q)for q in inputs};assert before==after and sha(obj)==oh
  for q in mods.values():assert sha(cache/Path(q['module'].replace('.','/')).with_suffix('.olean'))==q['object_sha256']
  _,depafter=H.dependency_libraries(root,a.library_path);assert deps==depafter
  d.update(status='PASS',after=after,all_input_provider_postchecks=True,module_object=dict(path=str(obj),sha256=oh),fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=sha(S))],all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=len(names),callers=caller_count,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except Exception as ex:d.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()
