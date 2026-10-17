"""Fresh local numeric command-preservation proof and audit only.

Successful StackCertificate and EnumeratorRun evidence identify the selected
23 imported project source/object pairs. EnumeratorRun is only a provider of
actual CommandStep dependencies here, not an imported scheduler assumption.
External caches are pinned and identified, not rebuilt or fully attested.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,tempfile,time
MODULE='BusyBeaver.ZFC.ArithmeticCommandPreservation254'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.'
SOURCE_SHA='3d6d0d2a46259317fe5d398469d718184ee279dbaf8a9eeecfa36d41632a7fc7'
AUDIT_SHA='d6ac7d3f4400738ecec3eb167c69eb1fc3486751e304d9053b437ec36764709b'
PROBES=['working_state','certified_state','someState_sub_one','old_le_witnessBound',
 'mem_le_witnessBound','prov_at_witnessBound','gate_witness','certified_mp_success',
 'certified_ax','effect_preserves','certified_step','certified_halt']

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ('repo','dependency-root','certificate-evidence','run-evidence'):p.add_argument('--'+key,type=Path,required=True)
 for key in ('certificate-cache','run-cache','source','audit','output','lean'):p.add_argument('--'+key,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use Python -O.')
 R=a.repo.resolve();root=a.dependency_root.resolve()
 W=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-preservation-'))
 assert not W.is_relative_to(R)and not W.is_relative_to(root)
 assert not W.exists()or(W.is_dir()and not any(W.iterdir())),'Output must be new or empty.'
 W.mkdir(parents=True,exist_ok=True)
 sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 spec=importlib.util.spec_from_file_location('preservation_cantor_helpers',helper);H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
 EP=a.certificate_evidence.resolve();FP=a.run_evidence.resolve();e,f=[json.loads(x.read_text())for x in(EP,FP)]
 for d in(e,f):assert d['status']=='PASS'and d['only_standard_axioms']is True and d['all_input_provider_postchecks']is True
 assert e['named_axiom_probes']==24 and e['callers']==17 and e['all_fresh_objects_unchanged_after_audit']is True
 assert f['named_axiom_probes']==16 and f['callers']==13
 C,version=H.compiler_path(a.lean)
 assert sha(C)==e['compiler']['sha256']==f['compiler']['sha256']and version==e['compiler']['version']==f['compiler']['version']
 libs,deps=H.dependency_libraries(root,a.library_path)
 for d in(e,f):
  for name in('Foundation','Mathlib'):
   assert deps[name]['pin']==d['dependencies'][name]['pin']and deps[name]['tracked_clean']is True and d['dependencies'][name]['tracked_clean']is True
  assert deps['lake_manifest_sha256']==d['dependencies']['lake_manifest_sha256']
  assert set(deps['providers'])==set(d['dependencies']['providers'])
  for n,q in deps['providers'].items():assert q['sha256']==d['dependencies']['providers'][n]['sha256']
 def project_source(m):
  rel=Path(m.replace('.','/')).with_suffix('.lean')
  if m=='FirstOrder.Fol':return R/'Logic/FirstOrder/Lean'/rel
  assert m.startswith('BusyBeaver.ZFC.');return R/'Computability/BusyBeaver/Lean'/rel
 candidates={}
 def add(q,cache):
  q=dict(q);m=q['module'];q['source']=str(project_source(m))
  if cache:q['object']=str(cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))
  candidates.setdefault(m,[]).append(q)
 for q in e['reused_modules']:add(q,a.certificate_cache)
 fresh=e.get('module_object')
 if fresh is None:
  assert len(e['fresh_modules'])==1;fresh=e['fresh_modules'][0]
  assert fresh['module']=='BusyBeaver.ZFC.ArithmeticStackCertificate254'and fresh['source_sha256']==e['source']['sha256']
 add(dict(module='BusyBeaver.ZFC.ArithmeticStackCertificate254',source=e['source']['path'],source_sha256=e['source']['sha256'],object=fresh['path'],object_sha256=fresh['sha256']),a.certificate_cache)
 for q in f['reused_modules']:add(q,a.run_cache)
 S=a.source.resolve()if a.source else project_source(MODULE)
 A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_command_preservation254_audit.lean'
 assert a.source is not None or sha(S)==SOURCE_SHA
 assert a.audit is not None or sha(A)==AUDIT_SHA
 imports=['BusyBeaver.ZFC.ArithmeticStackCertificate254','BusyBeaver.ZFC.ArithmeticCommandStep254']
 assert H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE]
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)
 assert names==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==15
 mods={};external=set();visiting=set()
 def visit(m):
  if m in mods:return
  assert m not in visiting and m in candidates;visiting.add(m);q=candidates[m][0]
  for n in H.lean_imports(Path(q['source']).read_text()):
   if n in candidates:visit(n)
   else:assert n.startswith(('Foundation.','Mathlib.'));external.add(n)
  visiting.remove(m);mods[m]=q
 for m in imports:visit(m)
 assert len(mods)==23
 alternatives=[]
 for m,chosen in mods.items():
  for q in candidates[m]:
   assert q['source_sha256']==chosen['source_sha256']
   assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256']
   if q['object_sha256']!=chosen['object_sha256']:
    assert m=='BusyBeaver.ZFC.ArithmeticCantor';alternatives.append(dict(q,used_as_provider=False))
 expected={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
 assert {q['module']for q in e['providers']}=={q['module']for q in f['providers']}==expected
 providers=[]
 for n in sorted(expected):
  rel=Path(n.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation'if n.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean');assert obj and src.is_file()
  q=dict(module=n,source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True)
  for d in(e,f):
   old=next(x for x in d['providers']if x['module']==n);assert q['source_sha256']==old['source_sha256']and q['object_sha256']==old['object_sha256']
  providers.append(q)
 assert external<=expected
 cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual=[]
 for q in list(mods.values())+providers:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(x/rel for x in[cache,*libs]if(x/rel).is_file());assert sha(obj)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
 selected_candidates=[q for m in mods for q in candidates[m]]
 inputs=[Path(__file__).resolve(),helper,EP,FP,C,S,A,ss,aa,root/'lake-manifest.json']
 for q in selected_candidates+providers:inputs.extend((Path(q['source']),Path(q['object'])))
 inputs.extend(Path(q['path'])for q in deps['providers'].values());inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,source_overridden=a.source is not None,audit_overridden=a.audit is not None,compiler=dict(path=str(C),version=version,sha256=sha(C)),certificate_evidence=dict(path=str(EP),sha256=sha(EP)),scheduler_run_provider_evidence=dict(path=str(FP),sha256=sha(FP)),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),reused_count=len(mods),same_source_object_alternatives=alternatives,providers=providers,actual_first_providers=actual,exact_project_import_closure=True,available_but_not_imported=sorted(set(candidates)-set(mods)),direct_external_imports=sorted(external),dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};assert before==after
  for q in list(mods.values())+providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next(x/rel for x in[cache,*libs]if(x/rel).is_file());assert sha(first)==q['object_sha256']
  _,da=H.dependency_libraries(root,a.library_path);assert deps==da
  return after
 save()
 if a.prepare_only:r.update(after=post(),all_input_provider_postchecks=True);save();print(W/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();p=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=p.stdout+p.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=p.returncode,output=out));save();assert p.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=sha(obj);out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  assert[n for n,_ in reports]==names and all(set(x.strip()for x in a.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,a in reports)
  after=post();assert sha(obj)==oh
  r.update(status='PASS',after=after,all_input_provider_postchecks=True,all_fresh_objects_unchanged_after_audit=True,module_object=dict(path=str(obj),sha256=oh),fresh_modules=[dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S))],named_axiom_probes=12,callers=15,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()
