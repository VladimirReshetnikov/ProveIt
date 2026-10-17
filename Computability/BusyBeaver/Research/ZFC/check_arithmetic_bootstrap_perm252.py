"""Guarded fresh fixed frozen252 arithmetic bootstrap transport check.

Only the supplied Bootstrap source and audit are built. The maintained machine
arithmetic record supplies24 project providers; the independent successful
bootstrap/core record supplies the one BootPerm252 provider (25 total). Existing pinned
Foundation/Mathlib objects are reused, not built or downloaded.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ('repo','dependency-root','machine-evidence','bootstrap-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
 p.add_argument('--prepare-only',action='store_true')
 for k in ('source','audit','cache','bootstrap-cache','full-machine-evidence','lean'):p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
 h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('cantor_helpers',helper);H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
 E=a.machine_evidence.resolve();e=json.loads(E.read_text());assert e['status']=='PASS'and e['only_standard_axioms']is True and e['all_source_and_reused_object_identities_unchanged_after_check']is True and e['PRF_Seq_and_dependency_provider_identities_unchanged_after_check']is True
 assert e['total_named_axiom_probes']==196 and e['total_callers']==237
 if 'full_evidence'in e:
  F=a.full_machine_evidence.resolve()if a.full_machine_evidence else Path(e['full_evidence']['path']);assert h(F)==e['full_evidence']['sha256'];full=json.loads(F.read_text())
 else:
  assert a.full_machine_evidence is None;F=E;full=e
 assert full['status']=='PASS'and full['only_standard_axioms']is True
 assert full['all_source_and_reused_object_identities_unchanged_after_check']is True and full['PRF_Seq_and_dependency_provider_identities_unchanged_after_check']is True
 C,version=H.compiler_path(a.lean);assert h(C)==e['compiler_binary_sha256']and version==e['compiler']['version']
 libs,deps=H.dependency_libraries(D,a.library_path)
 for name in ('Foundation','Mathlib'):assert deps[name]['pin']==e['dependencies'][name]['pin']and deps[name]['tracked_clean']is True and e['dependencies'][name]['tracked_clean']is True
 assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
 for name,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][name]['sha256']
 def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
 mods={}
 for q in e['reused_core']:
  m=q['module'];mods[m]=dict(module=m,source=str(source(m)),source_sha256=q['source_sha256'],object=q['olean'],object_sha256=q['olean_sha256'])
 if all(isinstance(q,dict)for q in e['fresh_modules']):
  for q in e['fresh_modules']:
   m=q['module'];mods[m]=dict(module=m,source=str(source(m)),source_sha256=q['source']['sha256'],object=q['module_object']['path'],object_sha256=q['module_object']['sha256'])
 else:
  assert all(isinstance(q,str)for q in e['fresh_modules'])
  assert len(e['fresh_arithmetic_prerequisite_objects'])==5 and len(e['new_modules'])==3
  for q in e['fresh_arithmetic_prerequisite_objects']:
   m=q['module'];suffix='Computability/BusyBeaver/Lean/'+m.replace('.','/')+'.lean';hashes={v for k,v in e['inputs'].items()if k.endswith(suffix)};assert len(hashes)==1
   mods[m]=dict(module=m,source=str(source(m)),source_sha256=hashes.pop(),object=q['path'],object_sha256=q['sha256'])
  for q in e['new_modules']:
   m=q['module'];mods[m]=dict(module=m,source=str(source(m)),source_sha256=q['source']['sha256'],object=q['module_object']['path'],object_sha256=q['module_object']['sha256'])
  assert set(e['fresh_modules'])=={q['module']for q in e['fresh_arithmetic_prerequisite_objects']}|{q['module']for q in e['new_modules']}
 BE=a.bootstrap_evidence.resolve();boot_record=json.loads(BE.read_text())
 assert boot_record['compiler']['sha256']==h(C)and boot_record['compiler']['version']==version
 assert boot_record['status']=='PASS168-unit source-verified integration'and boot_record['only_standard_axioms']is True
 assert all(boot_record[k]is True for k in ['all_source_identities_unchanged_after_check','all_object_identities_unchanged_after_check','all_reused_object_identities_unchanged_after_check'])
 boot=next(q for q in boot_record['source_closure']if q['module']=='BusyBeaver.ZFC.BootPerm252')
 assert boot['sha256']==boot['post_source_sha256']and boot['olean_sha256']==boot['post_olean_sha256']
 m=boot['module'];mods[m]=dict(module=m,source=str(source(m)),source_sha256=boot['sha256'],object=boot['olean'],object_sha256=boot['olean_sha256'])
 assert len(mods)==25
 if a.cache:
  for q in mods.values():q['object']=str(a.cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
 if a.bootstrap_cache:mods['BusyBeaver.ZFC.BootPerm252']['object']=str(a.bootstrap_cache.resolve()/'BusyBeaver/ZFC/BootPerm252.olean')
 for q in mods.values():assert h(q['source'])==q['source_sha256']and h(q['object'])==q['object_sha256']
 external_expected={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Arithmetic.Definability.Absoluteness'}
 providers=[];prior={q['module']:q for q in full['fresh_prerequisite']['iteration_providers']}
 for m in sorted(external_expected):
  rel=Path(m.replace('.','/'));obj=next((p/rel.with_suffix('.olean')for p in libs if(p/rel.with_suffix('.olean')).is_file()),None);dep='Foundation'if m.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean');assert obj and src.is_file()
  if m in prior:assert h(obj)==prior[m]['object_sha256']and h(src)==prior[m]['source_sha256']
  elif m=='Foundation.FirstOrder.Arithmetic.Definability.Absoluteness':
   assert h(src)=='a9d76ab1d72ec80b05ce303fe319214b1bdd79b9d00c616e5e25620bad329f88'and h(obj)=='a8135c41a4230561cfd902191fe6e9d4499c5aac8cb5b210eeed26e0b7cb7172'
  else:assert h(obj)==e['dependencies']['providers'][m]['sha256']
  providers.append(dict(module=m,source=str(src),source_sha256=h(src),object=str(obj.resolve()),object_sha256=h(obj),actual_first_provider=True))
 S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticBootstrapPerm252.lean'
 A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_bootstrap_perm252_audit.lean'
 assert a.source is not None or h(S)=='d1b2c82096a61b61c21a411bc11f336d7010616c78a942367cf024926528d290'
 assert a.audit is not None or h(A)=='1510cb6753f188c9bfc85b3a10d6187b8bd34ae87479c0b145d9b1f0d4ff075e'
 module='BusyBeaver.ZFC.ArithmeticBootstrapPerm252';prefix='SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252.'
 expected_names=['bitsCode_zero_of_blank','bitsCode_ext','encodeZip_unique','numericRun_of_zipRep','standard_boot','run_cast','internal_boot','runEquationSentence_eval','bootstrapSentence_true','isigma1_proves_bootstrap','peano_proves_bootstrap']
 assert H.lean_imports(S.read_text())==['BusyBeaver.ZFC.ArithmeticMachineRunPerm252','BusyBeaver.ZFC.BootPerm252','Foundation.FirstOrder.Arithmetic.Definability.Absoluteness']and H.lean_imports(A.read_text())==[module]
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);assert names==[prefix+n for n in expected_names]and len(re.findall(r'^example\b',A.read_text(),re.M))==13
 required={};external=set();visiting=set()
 def visit(m):
  if m in required:return
  assert m not in visiting and m in mods;visiting.add(m);q=mods[m]
  for n in H.lean_imports(Path(q['source']).read_text()):
   if n in mods:visit(n)
   else:assert n.startswith(('Foundation.','Mathlib.','Lean.'));external.add(n)
  visiting.remove(m);required[m]=q
 for m in H.lean_imports(S.read_text()):
  if m.startswith(('Foundation.','Mathlib.','Lean.')):external.add(m)
  else:visit(m)
 assert set(required)==set(mods)
 cache=W/'cache';cache.mkdir();snap=W/'sources';local=snap/'BusyBeaver/ZFC';local.mkdir(parents=True)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual=[]
 for q in list(mods.values())+providers:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next(p/rel for p in[cache,*libs]if(p/rel).is_file());assert h(first)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(first),resolved=str(first.resolve()),sha256=h(first)))
 toolchain=[];toolchain_root=C.parent.parent/'lib/lean'
 for m in sorted(external-external_expected):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolchain_root/rel;assert reference.is_file()
  obj=next(p/rel for p in [cache,*libs,toolchain_root]if(p/rel).is_file());assert h(obj)==h(reference),'A different library shadows the compiler toolchain provider.'
  toolchain.append(dict(module=m,object=str(obj.resolve()),object_sha256=h(obj),actual_first=str(obj),actual_first_provider=True,toolchain_reference=str(reference),toolchain_reference_sha256=h(reference),scope='Actual first-selected object matches the existing toolchain reference; not independently rebuilt or historically hashed by the compact baseline.'))
 ss=local/S.name;aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 inputs=[Path(__file__).resolve(),helper,E,F,BE,C,S,A,ss,aa,D/'lake-manifest.json']
 for q in list(mods.values())+providers:inputs.extend([Path(q['source']),Path(q['object'])])
 inputs.extend(Path(q[k])for q in toolchain for k in ('object','toolchain_reference'));inputs=list(dict.fromkeys(p.resolve()for p in inputs));before={str(p):h(p)for p in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,compiler=dict(path=str(C),version=version,sha256=h(C)),machine_evidence=dict(path=str(E),sha256=h(E)),full_machine_evidence=dict(path=str(F),sha256=h(F)),bootstrap_evidence=dict(path=str(BE),sha256=h(BE)),new_direct_provider_note='Absoluteness matches the source/object pair identified in original Bootstrap run4; not inherited from machine-only evidence.',source=dict(path=str(S),sha256=h(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=h(A),snapshot=str(aa)),reused_count=len(mods),reused_modules=list(mods.values()),providers=providers,actual_first_providers=actual,toolchain_providers=toolchain,exact_project_import_closure=True,dependencies=deps,commands=[],before=before,LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 def post():
  after={str(p):h(p)for p in inputs};assert before==after
  for q in list(mods.values())+providers+toolchain:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next(p/rel for p in [cache,*libs,toolchain_root]if(p/rel).is_file());assert h(first)==q['object_sha256']
   if q in toolchain:assert str(first.resolve())==q['object']
  _,depafter=H.dependency_libraries(D,a.library_path);assert deps==depafter
  d.update(after=after,all_input_provider_postchecks=True)
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();r=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;(W/(label+'.log')).write_text(out);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=out));save();assert r.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/'BusyBeaver/ZFC/ArithmeticBootstrapPerm252.olean';run('source',ss,obj);oh=h(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names;assert all(set(s.strip()for s in v.split(',')if s.strip())<={'propext','Classical.choice','Quot.sound'}for _,v in reports)
  post();assert h(obj)==oh;d.update(status='PASS',fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=h(S))],all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=11,callers=13,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except Exception as ex:d.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()
