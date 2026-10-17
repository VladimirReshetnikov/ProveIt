"""Narrow represented internal equality-context and finite proof interface check.
Reuses exact checked environment and quantifier modules and actual ancestors.
Prepare-only makes no compiler/version call; no dependencies are built/fetched.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ValidatorEqualityContext254'
SOURCE_SHA='86af3af2debcf1999e32b3d6f8a3f7e5ccff0e722feca7be3e90b2c31bff0584'
AUDIT_SHA='35b44654b11bc3c93eb787ea01a46cd5ceb080a1a1656bfa21ce8a03fc84fb2f'
NAMES=['LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_defined', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_delta', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_defined', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_delta', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_zero', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefixContext_succ', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_nil', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_intro_imp', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_under', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_mono_right', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.conj_interchange', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefix_projection', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_projection', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.prefix_cons_equiv', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_forward', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_backward', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_head', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.eqContext_cons_tail', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.discharge_cons', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.under_cons', 'LeanProofs.ZFCinPA.ValidatorEqualityContext254.all_of_cons']
ENVIRONMENT_RECORD='9a0e14528cb4cb0786ae506492e4a4fad8a82af6d7f31adc155a0260792523e7'
QUANTIFIER_RECORD='a5d44ee88abad04bf5a3a6f6e9a470e2c1b72970cfa5063ea3129dfc300240ca'
PROJECTS=['BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCode254', 'BusyBeaver.ZFC.ArithmeticHistory254', 'BusyBeaver.ZFC.ArithmeticHistoryRecurrence254', 'BusyBeaver.ZFC.ArithmeticProofConstructors254', 'BusyBeaver.ZFC.ArithmeticRow254', 'BusyBeaver.ZFC.ArithmeticTemplates254', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.Code254History', 'BusyBeaver.ZFC.Code254Proof', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'FirstOrder.Fol', 'ZFCinPA.Instances', 'ZFCinPA.ValidatorEnvironmentLabels254', 'ZFCinPA.ValidatorFormulaEncoder254', 'ZFCinPA.ValidatorProvability254', 'ZFCinPA.ValidatorQuantifierCore254']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def default_repo():
 for q in Path(__file__).resolve().parents:
  if(q/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return q
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo())
 p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 p.add_argument('--environment-evidence',type=Path);p.add_argument('--quantifier-evidence',type=Path)
 p.add_argument('--project-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--source',type=Path)
 p.add_argument('--audit',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve()
 S=(a.source or R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEqualityContext254.lean').resolve();A=(a.audit or R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEqualityContext254Audit.lean').resolve()
 E=(a.environment_evidence or R/'Logic/Interpretability/ZFCinPA/results/validator-environment-labels254-verification.json').resolve()
 P=(a.quantifier_evidence or R/'Logic/Interpretability/ZFCinPA/results/validator-quantifier-core254-verification.json').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or(W.is_dir()and not any(W.iterdir()))),'Fresh external output required.')
 req((sha(S),sha(A))==(SOURCE_SHA,AUDIT_SHA),'Changed frozen source/audit.')
 req(sha(E)==ENVIRONMENT_RECORD and sha(P)==QUANTIFIER_RECORD,'Wrong exact checked environment/quantifier records.')
 e=json.loads(E.read_text());p_record=json.loads(P.read_text());records=[e,p_record]
 for parent,counts,source_hash,audit_hash in [
  (e,(39,28),'c7735da0c060c645a2285ec96fe7cec3f50feb5ec8873d06f270831a71fe2e66','c8d529acc50abc16e8532ed24d7719fabcbcaabee7623868ebedf96d1adfd10a'),
  (p_record,(25,18),'4afb9947d05cf713b74c16cb8162af5b0e6c03461ed87e21cbdf1da3303ea2f1','e66efc5fed7547b51ec97225e6d6ae92b4d91be68a8a42fdc26c235eac339e6b')]:
  req(parent['status']=='PASS'and(parent['named_axiom_probes'],parent['callers'])==counts and parent['only_standard_axioms']and parent['all_input_provider_postchecks']and parent['all_fresh_objects_unchanged_after_audit'],'Wrong parent PASS contract.')
  req((parent['source']['sha256'],parent['audit']['sha256'])==(source_hash,audit_hash),'Wrong frozen parent source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 for r in records:
  helper_hashes={v for k,v in r['before'].items()if k.endswith('/Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py')}
  req(helper_hashes=={sha(helper)},'Different exact parent discovery helper.')
 sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C=(a.lean or Path(e['compiler']['path'])).expanduser().resolve();version=e['compiler']['version']
 for r in records:req(sha(C)==r['compiler']['sha256']and version==r['compiler']['version'],'Different compiler binary/version.')
 req(version.startswith('Lean (version 4.32.0,'),'Wrong recorded toolchain version.')
 if not a.prepare_only:req(subprocess.check_output([str(C),'--version'],text=True).strip()==version,'Different observed compiler version.')
 libs,deps=H.dependency_libraries(D,a.library_path)
 for r in records:
  for n in ['Foundation','Mathlib']:req(deps[n]['pin']==r['dependencies'][n]['pin']and deps[n]['tracked_clean']and r['dependencies'][n]['tracked_clean'],'Different dependency pin/clean state.')
  req(deps['lake_manifest_sha256']==r['dependencies']['lake_manifest_sha256'],'Different manifest.')
  req(set(deps['providers'])==set(r['dependencies']['providers']),'Different discovery anchor set.')
  for m,q in deps['providers'].items():req(q['sha256']==r['dependencies']['providers'][m]['sha256'],'Different discovery provider '+m)
 prior={};boundary={}
 for r in records:
  for q in r['reused_modules']:
   if q['module']in prior:req((q['source_sha256'],q['object_sha256'])==(prior[q['module']]['source_sha256'],prior[q['module']]['object_sha256']),'Different shared project '+q['module'])
   else:prior[q['module']]=q
  for q in r['providers']:
   if q['module']in boundary:req((q['source_sha256'],q['object_sha256'])==(boundary[q['module']]['source_sha256'],boundary[q['module']]['object_sha256']),'Different shared external '+q['module'])
   else:boundary[q['module']]=q
 for parent,module,source_hash,object_hash in [
  (e,'ZFCinPA.ValidatorEnvironmentLabels254','c7735da0c060c645a2285ec96fe7cec3f50feb5ec8873d06f270831a71fe2e66','a9b3498997becb0574a91a4e0000dc556d9863bcd0a978e1db1235bbdb9ff7dc'),
  (p_record,'ZFCinPA.ValidatorQuantifierCore254','4afb9947d05cf713b74c16cb8162af5b0e6c03461ed87e21cbdf1da3303ea2f1','23aec68314992d3b63c020f2c4abb3daf3cad038e663dbdfc663fb792ed68c0f')]:
  fresh,=parent['fresh_modules'];req((fresh['module'],fresh['source_sha256'],fresh['sha256'])==(module,source_hash,object_hash),'Wrong checked parent fresh object.')
  prior[module]=dict(module=module,source_sha256=source_hash,object=fresh['path'],object_sha256=object_hash)
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing supplied Foundation namespace.')
 selected={};external={};visiting=set();roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean'}
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Project import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];ss=(R/roots[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=(a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])).resolve()
   req((sha(ss),sha(o))==(old['source_sha256'],old['object_sha256']),'Changed selected project '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded actual external import '+m);old=boundary[m];dr=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=dr/rel.with_suffix('.lean');o=next((x/rel.with_suffix('.olean')for x in [namespace.parent,*libs]if(x/rel.with_suffix('.olean')).is_file()),None)
   req(o is not None and(sha(ss),sha(o))==(old['source_sha256'],old['object_sha256']),'Changed actual external boundary '+m)
   external[m]=dict(module=m,source=str(ss.resolve()),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope='Actual direct project import boundary; no whole/transitive namespace attestation.')
  visiting.remove(m)
 imports=['ZFCinPA.ValidatorQuantifierCore254','ZFCinPA.ValidatorEnvironmentLabels254']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong exact source/audit imports.')
 for m in imports:visit(m)
 req(set(selected)==set(PROJECTS)and len(external)==5,'Wrong exact 24-project/five-direct-boundary import closure.')
 req(set(external)=={'Mathlib.Tactic.Ring', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Foundation.FirstOrder.Arithmetic.HFS.PRF'},'Wrong actual external boundary set.')
 req(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==NAMES and len(NAMES)==21 and len(re.findall(r'^example\b',A.read_text(),re.M))==24,'Wrong 21/24 audit contract.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dst=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 files=[S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())];direct={m for file in files for m in H.lean_imports(file.read_text())if m in {'Init','Std','Lean'}or m.startswith(('Lean.','Std.'))};tool=[];sysroot=C.parent.parent/'lib/lean';search=[cache,*libs,sysroot]
 for m in sorted(direct|{'Init','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');ref=sysroot/rel;o=next((x/rel for x in search if(x/rel).is_file()),None)
  req(o is not None and ref.is_file()and sha(o)==sha(ref),'Wrong actual/canonical toolchain provider '+m)
  for r in records:
   for old in r.get('toolchain_providers',[]):
    if old['module']==m:req(sha(o)==old['object_sha256'],'Different parent toolchain boundary '+m)
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref)))
 inputs=[Path(__file__).resolve(),helper,E,P,C,D/'lake-manifest.json',S,A,ss,aa]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']];inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):sha(x)for x in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Fixed total Sigma1/Delta1 internal equality-context prefix, indexed CProv projections, both cons implications and body-IH currying under IΣ1, with four-vacuity-premise quantifier client. No source-formula alpha induction, global proof renaming, source-proof compiler or consistency endpoint.',parent_evidence=[dict(role='Checked Environment39/28 and exact ancestors',path=str(E),sha256=sha(E)),dict(role='Checked Quantifier25/18 and exact ancestors',path=str(P),sha256=sha(P))],parent_fresh_module_imported=True,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),compiler=dict(path=str(C),sha256=sha(C),version=version),compiler_version_query_performed=not a.prepare_only,reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),unused_parent_modules=sorted(set(prior)-set(selected)),unused_parent_external_modules=sorted(set(boundary)-set(external)),namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace),whole_namespace_independently_attested=False),dependencies=deps,exact_project_import_closure=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,per_command_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
 def post():
  r['after']={str(x):sha(x)for x in inputs};req(before==r['after'],'Changed immutable input.')
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next((x/rel for x in search if(x/rel).is_file()),None);req(o is not None and o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic()
  try:cp=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True,timeout=120);out=cp.stdout+cp.stderr;code=cp.returncode;timeout=False
  except subprocess.TimeoutExpired as ex:
   def text(v):return v.decode(errors='replace')if isinstance(v,bytes)else(v or'')
   out=text(ex.stdout)+text(ex.stderr);code=None;timeout=True
  (W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=code,timed_out=timeout,output=out));save();req(not timeout,'Compiler timeout; FAIL retained.');req(code==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 try:
  if a.prepare_only:post();save();print(W/'verification.json');return
  o=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run('source',ss,o);oh=sha(o)
  r.update(source_passed=True,fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],fresh_object_sha256_before_audit=oh);save()
  req(sha(o)==oh,'Changed fresh source object before audit.')
  out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==NAMES and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong ordered axiom reports.')
  post();req(sha(o)==oh,'Changed fresh object.');r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=21,callers=24,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
