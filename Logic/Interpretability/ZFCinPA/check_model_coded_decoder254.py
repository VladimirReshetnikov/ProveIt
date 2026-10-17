"""Check only the represented C254 decoder/audit against two exact cached proof records."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, time
MODULE='ZFCinPA.ModelCodedDecoder254'
PREFIX='LeanProofs.ZFCinPA.ModelCodedDecoder254.'
NAMES=['atomCode_defined','zeroFormula_defined','row_defined','history_defined','history_seq','history_length','decode_defined','history_lookup_le','history_lookup','decode_zero','decode_succ_row','child_bounds','row_isFormula','history_formulas','decode_isFormula','decode_succ']
ZFCPROJECTS={'ZFCinPA.Instances','ZFCinPA.SchemaClosure','ZFCinPA.SeparationDelta1','ZFCinPA.ReplacementDelta1','ZFCinPA.ZFDelta1','ZFCinPA.ModelCodedSchemaAxioms','ZFCinPA.ModelCodedBindFree','ZFCinPA.ModelCodedClosedSchemaAxioms','ZFCinPA.ModelCodedSpecialization','ZFCinPA.ModelCodedBindOne'}
NATIVE={'FirstOrder.Fol','BusyBeaver.ZFC.Kalmar','BusyBeaver.ZFC.TarskiCalculus','BusyBeaver.ZFC.TarskiDerived','BusyBeaver.ZFC.TarskiLeibniz','BusyBeaver.ZFC.TarskiClean','BusyBeaver.ZFC.TarskiComplete','BusyBeaver.ZFC.Lukasiewicz','BusyBeaver.ZFC.TarskiFalsity','BusyBeaver.ZFC.Code254','BusyBeaver.ZFC.ArithmeticCantor'}
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
SOURCE_SHA256='1f471e17aa569a342e6e98b0985a86a7837a34b434bfedf35019e7e4014ba6e0'
AUDIT_SHA256='04f889d0ec4e0cfd7cf8d8038b8003908eda3128d15435024e9aff1c66715ff9'
def default_repo():
 for q in Path(__file__).resolve().parents:
  if(q/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return q
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo());p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 for k in ['bind-one-evidence','cantor-evidence','source','audit']:p.add_argument('--'+k,type=Path)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--bind-one-cache',type=Path);p.add_argument('--native-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';B=(a.bind_one_evidence or P/'results/model-coded-bind-one-verification.json').resolve();E=(a.cantor_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-cantor-verification.json').resolve();S=(a.source or P/'Lean/ZFCinPA/ModelCodedDecoder254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedDecoder254Audit.lean').resolve();W=a.output.resolve()
 req(sha(S)==SOURCE_SHA256 and sha(A)==AUDIT_SHA256,'Wrong frozen source/audit.')
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);b=json.loads(B.read_text());e=json.loads(E.read_text())
 req(b['status']=='PASS'and b['named_axiom_probes']==15 and b['callers']==19 and b['only_standard_axioms']and b['all_input_provider_postchecks']and b['all_fresh_objects_unchanged_after_audit'],'Wrong BindOne proof contract.')
 req(b['source']['sha256']=='78f5858a715e74bca2af835ec990e33775f588219ef7f30b217825acbffd6785'and b['audit']['sha256']=='29467fe36a55a048fb04d136ec59926b9b8fd02ef79883d9912c129ac5c825da','Wrong BindOne source/audit.')
 req(e['status']=='PASS'and e['named_axiom_probes']==27 and e['callers']==20 and e['only_standard_axioms']and e['source_unchanged_after_check']and e['reused_core_unchanged_after_check'],'Wrong native Cantor proof contract.')
 req(e['source']['sha256']=='aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84'and e['audit_source']['sha256']=='1c6927ed924d1075fb248a984825f0a65fec53fb43ee2c19d7c3bb795579a2a2','Wrong native Cantor source/audit.')
 req(sha(C)==b['compiler']['sha256']and version==b['compiler']['version']==e['compiler']['version'],'Different compiler identity/version.')
 for old in [b,e]:
  for dep in ['Foundation','Mathlib']:req(deps[dep]['pin']==old['dependencies'][dep]['pin']and deps[dep]['tracked_clean']and old['dependencies'][dep]['tracked_clean'],'Different dependency pin/state.')
  req(deps['lake_manifest_sha256']==old['dependencies']['lake_manifest_sha256'],'Different lake manifest.')
  for m,q in deps['providers'].items():req(q['sha256']==old['dependencies']['providers'][m]['sha256'],'Different base provider in parent evidence.')
 prior={q['module']:dict(q,parent='BindOne')for q in b['reused_modules']};fresh=b['fresh_modules'][0]
 req(fresh['module']=='ZFCinPA.ModelCodedBindOne'and fresh['source_sha256']==b['source']['sha256'],'Wrong BindOne fresh object binding.')
 prior[fresh['module']]=dict(module=fresh['module'],source_sha256=fresh['source_sha256'],object=fresh['path'],object_sha256=fresh['sha256'],parent='BindOne')
 req({q['module']for q in e['reused_core']}==NATIVE-{'BusyBeaver.ZFC.ArithmeticCantor'},'Wrong exact native core.')
 for q in e['reused_core']:prior[q['module']]=dict(module=q['module'],source_sha256=q['source_sha256'],object=q['olean'],object_sha256=q['olean_sha256'],parent='Cantor')
 prior['BusyBeaver.ZFC.ArithmeticCantor']=dict(module='BusyBeaver.ZFC.ArithmeticCantor',source_sha256=e['source']['sha256'],object=e['module_object']['path'],object_sha256=e['module_object']['sha256'],parent='Cantor')
 boundary={q['module']:q for q in b['providers']};selected={};external={};visiting=set()
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(b['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 def source(m):
  rel=Path(m.replace('.','/')).with_suffix('.lean')
  if m.startswith('ZFCinPA.'):return R/'Logic/Interpretability/ZFCinPA/Lean'/rel
  if m.startswith('BusyBeaver.'):return R/'Computability/BusyBeaver/Lean'/rel
  if m.startswith('FirstOrder.'):return R/'Logic/FirstOrder/Lean'/rel
  raise RuntimeError('Unknown project namespace '+m)
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];s=source(m);override=a.bind_one_cache if old['parent']=='BindOne'else a.native_cache;o=override/rel.with_suffix('.olean')if override else Path(old['object'])
   req(sha(s)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected project source/object '+m)
   selected[m]=dict(module=m,source=str(s),source_sha256=sha(s),object=str(o.resolve()),object_sha256=sha(o),parent_evidence=old['parent'])
   for n in H.lean_imports(s.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];d=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);s=d/rel.with_suffix('.lean');o=next((q/rel.with_suffix('.olean')for q in [namespace.parent,*libs]if(q/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(s)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external source/object '+m)
   external[m]=dict(module=m,source=str(s),source_sha256=sha(s),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Recorded cached boundary, no whole-cache attestation.'))
  visiting.remove(m)
 imports=['ZFCinPA.ModelCodedBindOne','BusyBeaver.ZFC.ArithmeticCantor']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong direct imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 req(set(selected)==ZFCPROJECTS|NATIVE and set(external)==set(boundary),'Wrong exact 21-project/six-boundary union.')
 # Both native boundary providers must be exactly the selected shared boundaries.
 for m,q in e['dependencies']['providers'].items():req(external[m]['object_sha256']==q['sha256'],'Disagreeing native/BindOne boundary identity.')
 parent_audits=[R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedBindOneAudit.lean',R/'Computability/BusyBeaver/Research/ZFC/arithmetic_cantor_audit.lean']
 req(sha(parent_audits[0])==b['audit']['sha256']and sha(parent_audits[1])==e['audit_source']['sha256'],'Changed parent focused audit bytes.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==24,'Wrong focused16/24 audit.')
 W.mkdir(parents=True);cache=W/'cache';(cache/'ZFCinPA').mkdir(parents=True);(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/'ZFCinPA/ModelCodedDecoder254.lean';ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 toolroot=C.parent.parent/'lib/lean';tool=[];direct={m for f in [S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]for m in H.lean_imports(f.read_text())if m.startswith('Lean.')}
 for m in sorted(direct|{'Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((q/rel for q in [cache,*libs,toolroot]if(q/rel).is_file()),None);req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in b.get('toolchain_providers',[]):
   if old['module']==m:req(sha(o)==old['object_sha256'],'Changed BindOne toolchain provider.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,B,E,C,S,A,ss,aa,D/'lake-manifest.json',*parent_audits]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']];inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Fixed Sigma1 literal formula decoder by code-indexed history; no twelve-rule proof translation or PA consistency comparison.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),bind_one_evidence=dict(path=str(B),sha256=sha(B)),cantor_evidence=dict(path=str(E),sha256=sha(E),compiler_scope='Historical exact version; current binary additionally fixed by BindOne hash.'),reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,exact_project_import_closure=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(qp/rel for qp in [cache,*libs,toolroot]if(qp/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)];t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save();req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/'ZFCinPA/ModelCodedDecoder254.olean';run('source',ss,o);oh=sha(o);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);req([n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<=STANDARD for _,ax in reports),'Wrong axiom reports.');post();req(sha(o)==oh,'Changed fresh object.');r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=16,callers=24,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
