"""Narrow one-source decoded Lukasiewicz axiom check; no dependency build or fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedDecoderLukasiewicz254';PREFIX='LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254.'
NAMES=['decoded_imp_equiv','decoded_imp_congr','rho8Template','decoded_rho8_equiv','decoded_rho8_provable']
PROJECTS=['BusyBeaver.ZFC.ArithmeticCode254','BusyBeaver.ZFC.ArithmeticTemplates254','BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'FirstOrder.Fol', 'ZFCinPA.Instances', 'ZFCinPA.ModelCodedBindFree', 'ZFCinPA.ModelCodedBindOne', 'ZFCinPA.ModelCodedClosedSchemaAxioms', 'ZFCinPA.ModelCodedDecoder254', 'ZFCinPA.ModelCodedDecoderConstructors254', 'ZFCinPA.ModelCodedDecoderPropositional254', 'ZFCinPA.ModelCodedSchemaAxioms', 'ZFCinPA.ModelCodedSpecialization', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.ZFDelta1']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
SOURCE_SHA256='1279fb958e936e536b0cb44c11a069b068b4893117cc3b22c354002743704f89'
AUDIT_SHA256='86024fbc0312fff21e66bb5076cde53dc0fe4329ef8a3b05133ff35aa8d24510'
def default_repo():
 for q in Path(__file__).resolve().parents:
  if(q/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return q
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo());p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 for key in ['decoder-evidence','templates-evidence','source','audit']:p.add_argument('--'+key,type=Path)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--decoder-cache','--closed-cache',dest='closed_cache',type=Path,help='Optional consolidated cache with all twenty-six exact predecessor objects.')
 p.add_argument('--namespace-cache',type=Path,help='Optional cache root containing the complete Foundation namespace mirror.')
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.');R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';E=(a.decoder_evidence or P/'results/model-coded-decoder-propositional254-verification.json').resolve();E2=(a.templates_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-symbolic-boxes-perm252-verification.json').resolve();S=(a.source or P/'Lean/ZFCinPA/ModelCodedDecoderLukasiewicz254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedDecoderLukasiewicz254Audit.lean').resolve();W=a.output.resolve()
 req(sha(S)==SOURCE_SHA256 and sha(A)==AUDIT_SHA256,'Wrong frozen source/audit.')
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H);C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);e=json.loads(E.read_text())
 req(e['status']=='PASS'and e['named_axiom_probes']==9 and e['callers']==14 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong predecessor contract.')
 req(e['source']['sha256']=='8039464c514ba3a3d92b701348b1bd58cecd1cafb45c2ca40966db74aec3cce4'and e['audit']['sha256']=='8babd1b8b5f13fd625541cee1253418c82d3284d6279342decb568aa8e0b41d7','Wrong predecessor source/audit.')
 req(sha(C)==e['compiler']['sha256']and version==e['compiler']['version'],'Different compiler.')
 for dep in ['Foundation','Mathlib']:req(deps[dep]['pin']==e['dependencies'][dep]['pin']and deps[dep]['tracked_clean']and e['dependencies'][dep]['tracked_clean'],'Different dependency pin/state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Different manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Different base provider.')
 prior={q['module']:q for q in e['reused_modules']};new=e['fresh_modules'][0];req(new['module']=='ZFCinPA.ModelCodedDecoderPropositional254'and new['source_sha256']==e['source']['sha256'],'Wrong predecessor fresh module.');prior[new['module']]=dict(module=new['module'],source_sha256=new['source_sha256'],object=new['path'],object_sha256=new['sha256'])
 e2=json.loads(E2.read_text())
 req(e2['status']=='PASS'and e2['named_axiom_probes']==17 and e2['callers']==20 and e2['only_standard_axioms']and e2['all_input_provider_postchecks']and e2['all_fresh_objects_unchanged_after_audit'],'Wrong templates provider contract.')
 req(e2['source']['sha256']=='ae544a5d0bf0ba7ac830abca41b31fb1c52e5e6308faa4f61fa1c2812f411a4f'and e2['audit']['sha256']=='e87b3495dc73e2b241f90b7d826a8ae6238b4ddc5e0e962ffc56496da7bee67f','Wrong templates parent source/audit.')
 req(e2['compiler']==e['compiler'],'Different templates compiler.')
 for dep in ['Foundation','Mathlib']:req(e2['dependencies'][dep]['pin']==deps[dep]['pin']and e2['dependencies'][dep]['tracked_clean'],'Different templates dependency pin/state.')
 req(e2['dependencies']['lake_manifest_sha256']==deps['lake_manifest_sha256'],'Different templates manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==e2['dependencies']['providers'][m]['sha256'],'Different templates base provider.')
 additional={x['module']:x for x in e2['reused_modules']}
 variants=[]
 for m,x in prior.items():
  if m not in additional:continue
  y=additional[m];req(x['source_sha256']==y['source_sha256'],'Inconsistent shared source '+m)
  if x['object_sha256']!=y['object_sha256']:
   req(m=='BusyBeaver.ZFC.ArithmeticCantor'and x['source_sha256']=='aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84'
       and x['object_sha256']=='bf2ee28833f61c6c9c44244cb22ec8932c6a3570beed1e94749b2ab1e6b9cc71'
       and y['object_sha256']=='ff1e2f291d3d81940552aeb6a2a221dbfefd032005b10c9ca4d20ba4b84fb3b8','Unrecorded compiled variant '+m)
   req(sha(y['object'])==y['object_sha256'],'Changed unused checked variant '+m)
   variants.append(dict(module=m,source_sha256=x['source_sha256'],selected_object=x['object'],selected_sha256=x['object_sha256'],
     unused_recorded_object=y['object'],unused_recorded_sha256=y['object_sha256'],
     reason='Identical checked source and compiler/dependency pins; keep MP original as actual first provider and bind both individually recorded artifacts.'))
 for m in ['BusyBeaver.ZFC.ArithmeticTemplates254','BusyBeaver.ZFC.ArithmeticCode254']:prior[m]=additional[m]
 boundary={q['module']:q for q in e['providers']};selected={};external={};visiting=set()
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean'};ss=R/roots[m.split('.')[0]]/rel.with_suffix('.lean');o=a.closed_cache/rel.with_suffix('.olean')if a.closed_cache else Path(old['object']);req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected predecessor '+m);selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];dp=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=dp/rel.with_suffix('.lean');o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None);req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m);external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Recorded source/object boundary; no whole-cache attestation.'))
  visiting.remove(m)
 req(H.lean_imports(S.read_text())==['ZFCinPA.ModelCodedDecoderPropositional254','BusyBeaver.ZFC.ArithmeticTemplates254'],'Wrong new imports.');req(H.lean_imports(A.read_text())==[MODULE],'Wrong audit imports.')
 visit('ZFCinPA.ModelCodedDecoderPropositional254');visit('BusyBeaver.ZFC.ArithmeticTemplates254')
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS) and set(external)==set(boundary),'Wrong exact project closure.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==8,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';(cache/'ZFCinPA').mkdir(parents=True);(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/'ZFCinPA/ModelCodedDecoderLukasiewicz254.lean';ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 toolroot=C.parent.parent/'lib/lean';tool=[];direct={m for f in [S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]for m in H.lean_imports(f.read_text())if m.startswith('Lean.')}
 for m in sorted(direct|{'Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None);req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in e.get('toolchain_providers',[]):
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different predecessor toolchain object.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 parent_audit=R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedDecoderPropositional254Audit.lean';req(sha(parent_audit)==e['audit']['sha256'],'Changed parent audit.')
 inputs=[Path(__file__).resolve(),helper,E,E2,*[Path(q['unused_recorded_object'])for q in variants],C,S,A,ss,aa,D/'lake-manifest.json',parent_audit]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']];inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-model provability of the actual arithmetic rho8 row, with decoded implication alias handled by internal provable equivalence; no other axiom rows, full history transport or PA endpoint.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=dict(path=str(E),sha256=sha(E)),templates_provider_evidence=dict(path=str(E2),sha256=sha(E2)),shared_compiled_variants=variants,reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,exact_project_import_closure=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed first provider.')
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)];t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save();req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/'ZFCinPA/ModelCodedDecoderLukasiewicz254.olean';run('source',ss,o);oh=sha(o);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);req([n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(sha(o)==oh,'Changed fresh object.');r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=5,callers=8,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
