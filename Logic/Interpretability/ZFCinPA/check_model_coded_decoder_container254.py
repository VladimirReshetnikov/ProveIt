"""Exact internal C client from four frozen PASS parents; no dependency builds/fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedDecoderContainer254'
PREFIX='LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.'
SOURCE_SHA='71a24fa6ed39a9688a97562a4eafd12187bc10210a725e0a5ce3a4851dcf71b4'
AUDIT_SHA='067f9517f0a5a13fa82987e2d1e0120b06cdb531b1ccbc06791ed027928532c3'
NAMES=['interpret_im_congr','interpret_conj_congr','interpret_all_congr','interpret_ex_congr','interpret_container_native_equiv','zf_decoded_container_native_equiv','canonicalContainer_quote_subst','zf_canonicalContainer_provable','nativeContainer_distinct','zf_not_mem_self','namedExists_mono','zf_membershipContainer_outer','zf_named_membership_exists','zf_nativeContainer_coincident','zf_nativeContainer_provable','zf_decoded_bundleC_provable']
SPECS=[('circuits', 'model-coded-decoder-circuits254-verification.json', 'ZFCinPA.ModelCodedDecoderCircuits254', '60dca2bc4655490e462548e0eb66e5aeaa3664f0ec6c3b099025286a855c5c8a', 7, 10, '746b0e0d1f0b8960c5c76c5a0a57833a794c49da01620798ff29eefa962dbe67', '6addc5648c4739b5c59305caf9af2ce9c96ceb45d857d046c93706b520a3c3d5'), ('logical', 'model-coded-named-logical-normalization254-verification.json', 'ZFCinPA.ModelCodedNamedLogicalNormalization254', '67a8ce71d214fecf4af83ec32ea9df883f34e49bd4f8d9061cbc51e779113a42', 7, 10, '42a8a919d0c77fa7ac00f0c29fc45450afe49e69a28ab4a7923f74d791bd30da', '77fc039fcac043dec64b8e9762b6371fb3974fd7132b248f1e892263cbc45beb'), ('atomic', 'model-coded-decoder-atomic-vacuity254-verification.json', 'ZFCinPA.ModelCodedDecoderAtomicVacuity254', 'c8db05327dc3841e76162ab89aa09cab4a923dc56b0f9231cf8473bd83a4bdbe', 10, 12, 'e3cdebe04cb8e85bb115105c41dc2c764e52c91914cdfd3cd98a391bca947e14', 'ecc51d64d446034b783e97cb3cd9cd551332c6d5b6bda15614cc74001751840e'), ('native', 'native-zf-containers254-verification.json', 'ZFCinPA.NativeZFContainers254', '74bca8ad3e63c7bbf6f36eb501a13ece8ff99f5ffe716dbb045c1adfbc4cf3af', 15, 15, '0e44d1d054f58cfa8afba6851d82878f47e70ad0e6d05a80715d6467d875154b', '3e9d505e816157438df3e5218619401681f70ff96fd612cec93b3811e1e67d9f')]
PROJECTS=['BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.OmegaRecursion', 'BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCode254', 'BusyBeaver.ZFC.ArithmeticTemplates254', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.InternalOrd', 'BusyBeaver.ZFC.InternalRank', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.NamedZF', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'BusyBeaver.ZFC.ZFRank', 'FirstOrder.Calculus', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf', 'ZFCinPA.Instances', 'ZFCinPA.ModelCodedBindFree', 'ZFCinPA.ModelCodedBindOne', 'ZFCinPA.ModelCodedBinderAbsorption', 'ZFCinPA.ModelCodedClosedSchemaAxioms', 'ZFCinPA.ModelCodedDecoder254', 'ZFCinPA.ModelCodedDecoderAtomicVacuity254', 'ZFCinPA.ModelCodedDecoderCircuits254', 'ZFCinPA.ModelCodedDecoderConstructors254', 'ZFCinPA.ModelCodedDecoderEquality254', 'ZFCinPA.ModelCodedDecoderFalsity254', 'ZFCinPA.ModelCodedDecoderGeneralization254', 'ZFCinPA.ModelCodedDecoderLukasiewicz254', 'ZFCinPA.ModelCodedDecoderPropositional254', 'ZFCinPA.ModelCodedDecoderRho1_254', 'ZFCinPA.ModelCodedDecoderRho2_254', 'ZFCinPA.ModelCodedDecoderRho6_254', 'ZFCinPA.ModelCodedFreeRenaming', 'ZFCinPA.ModelCodedNamedBinderLaws', 'ZFCinPA.ModelCodedNamedLogicalNormalization254', 'ZFCinPA.ModelCodedNamedQuantifierTemplates254', 'ZFCinPA.ModelCodedProofRenaming', 'ZFCinPA.ModelCodedRenamingAxioms', 'ZFCinPA.ModelCodedRenamingBindOne', 'ZFCinPA.ModelCodedRenamingSets', 'ZFCinPA.ModelCodedSchemaAxioms', 'ZFCinPA.ModelCodedSpecialization', 'ZFCinPA.NativeZFContainers254', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.ZFDelta1']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def default_repo():
 for q in Path(__file__).resolve().parents:
  if(q/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return q
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo());p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 for key in ['source','audit']+[key+'-'+suffix for key,*_ in SPECS for suffix in ['evidence','source','audit']]:p.add_argument('--'+key,type=Path)
 p.add_argument('--project-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 S=(a.source or P/'Lean/ZFCinPA/ModelCodedDecoderContainer254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedDecoderContainer254Audit.lean').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 records=[];parent_evidence=[];parent_files=[];prior={};boundary={};source_overrides={};variants=[]
 for key,filename,module,recordhash,probes,callers,sourcehash,audithash in SPECS:
  path=(getattr(a,key+'_evidence')or P/'results'/filename).resolve();req(sha(path)==recordhash,'Wrong exact historical PASS record '+key)
  e=json.loads(path.read_text());records.append(e);parent_evidence.append(dict(key=key,path=str(path),sha256=sha(path)))
  req(e['status']=='PASS'and e['named_axiom_probes']==probes and e['callers']==callers and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong parent PASS contract '+key)
  req((e['source']['sha256'],e['audit']['sha256'])==(sourcehash,audithash),'Wrong parent source/audit '+key)
  req(len(e['fresh_modules'])==1 and e['fresh_modules'][0]['module']==module and e['fresh_modules'][0]['source_sha256']==sourcehash,'Wrong parent fresh object '+key)
  ss=(getattr(a,key+'_source')or P/'Lean'/Path(module.replace('.','/')).with_suffix('.lean')).resolve();aa=(getattr(a,key+'_audit')or P/'Lean/ZFCinPA'/(module.split('.')[-1]+'Audit.lean')).resolve()
  req(sha(ss)==sourcehash and sha(aa)==audithash,'Changed parent source/audit '+key);parent_files.extend([ss,aa]);source_overrides[module]=ss
  req(sha(C)==e['compiler']['sha256']and version==e['compiler']['version'],'Different compiler '+key)
  for dep in ['Foundation','Mathlib']:req(e['dependencies'][dep]['pin']==deps[dep]['pin']and e['dependencies'][dep]['tracked_clean']and deps[dep]['tracked_clean'],'Different dependency pin/state '+key)
  req(e['dependencies']['lake_manifest_sha256']==deps['lake_manifest_sha256'],'Different manifest '+key)
  for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Different dependency discovery anchor '+key)
  rows=e['reused_modules']+[dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256'])for q in e['fresh_modules']]
  for q in rows:
   m=q['module']
   if m in prior:req((q['source_sha256'],q['object_sha256'])==(prior[m]['source_sha256'],prior[m]['object_sha256']),'Inconsistent shared project '+m)
   else:prior[m]=q
  for q in e['providers']:
   m=q['module']
   if m in boundary:req((q['source_sha256'],q['object_sha256'])==(boundary[m]['source_sha256'],boundary[m]['object_sha256']),'Inconsistent shared boundary '+m)
   else:boundary[m]=q
  if key!='native':
   vv=e['inherited_shared_compiled_variants'];req(len(vv)==1,'Wrong numeric inherited variant count '+key);v=vv[0]
   req((v['module'],v['source_sha256'],v['selected_sha256'],v['unused_recorded_sha256'])==('BusyBeaver.ZFC.ArithmeticCantor','aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84','bf2ee28833f61c6c9c44244cb22ec8932c6a3570beed1e94749b2ab1e6b9cc71','ff1e2f291d3d81940552aeb6a2a221dbfefd032005b10c9ca4d20ba4b84fb3b8'),'Wrong exact inherited Cantor pair '+key)
   req(sha(v['unused_recorded_object'])==v['unused_recorded_sha256'],'Changed unused historical Cantor '+key);variants.append(v)
 req(len(variants)==3,'Wrong inherited numeric-parent count.')
 v=variants[0];req((prior[v['module']]['source_sha256'],prior[v['module']]['object_sha256'])==(v['source_sha256'],v['selected_sha256']),'Wrong selected Cantor identity.')
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(records[0]['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete existing Foundation namespace.')
 roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean','BoundedZFCConsistency':'SetTheory/BoundedConsistency/Lean','ZF':'SetTheory/ZF/Lean'}
 selected={};external={};visiting=set();tool_direct=set()
 def visit(m):
  if m in selected or m in external or m in tool_direct:return
  if m in {'Init','Std','Lean'}or m.startswith(('Init.','Std.','Lean.')):tool_direct.add(m);return
  req(m not in visiting,'Import cycle '+m);visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];req(m.split('.')[0]in roots,'Unexpected project root '+m);ss=(source_overrides.get(m)or R/roots[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected project '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];base=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=base/rel.with_suffix('.lean')
   o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m)
   external[m]=dict(module=m,source=str(ss.resolve()),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope='Selected direct source/object boundary; complete transitive namespace cache not independently rebuilt.')
  visiting.remove(m)
 imports=['ZFCinPA.ModelCodedDecoderCircuits254','ZFCinPA.ModelCodedNamedLogicalNormalization254','ZFCinPA.NativeZFContainers254','ZFCinPA.ModelCodedDecoderAtomicVacuity254']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong direct source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS)and set(external)==set(boundary),'Wrong exact selected closure.')
 req(all(module in selected for _,_,module,*_ in SPECS),'A parent fresh object is not actually imported.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==20,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 files=[S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]
 tool_direct.update(m for f in files for m in H.lean_imports(f.read_text())if m in {'Init','Std','Lean'}or m.startswith(('Init.','Std.','Lean.')))
 toolroot=C.parent.parent/'lib/lean';tool=[]
 for m in sorted(tool_direct|{'Init','Std','Lean','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in [q for e in records for q in e.get('toolchain_providers',[])]:
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different parent toolchain provider '+m)
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference),scope='Actual direct import'if m in tool_direct else'Implicit Init or explicit Std/Lean/Omega canonical guard anchor.'))
 inputs=[Path(__file__).resolve(),helper,C,S,A,ss,aa,D/'lake-manifest.json',*parent_files]+[Path(q['path'])for q in parent_evidence]+[Path(q['unused_recorded_object'])for q in variants]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Exact internal numerical C from fixed ordinary ZF row and finite native syntax, arbitrary internal labels, only actual c!=a/c!=b gates, a=b included. No G, bundle, accepted-proof translation or PA endpoint.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),parent_evidence=parent_evidence,reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(tool_direct),dependencies=deps,exact_project_import_closure=True,inherited_shared_compiled_variants=variants,all_four_parent_fresh_objects_imported=True,unused_parent_modules=sorted(set(prior)-set(selected)),before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)];t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save();req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run('source',ss,o);oh=sha(o);out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==names and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(sha(o)==oh,'Changed fresh object.')
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=16,callers=20,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
