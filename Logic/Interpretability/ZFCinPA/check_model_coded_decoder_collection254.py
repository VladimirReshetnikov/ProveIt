"""Exact internal numerical G from four frozen PASS parents; no dependency builds or PA endpoint."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedDecoderCollection254'
PREFIX='LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.'
SOURCE_SHA='64a133445dde69c2e642ab6397c2b72c51bd025f2843412a9d5bc8a8c2eeaa3e'
AUDIT_SHA='a9798acde4a76cdf640fbb3bed348c5824dfbc5fe87c51eef24ab2605d117544'
NAMES=['binaryBody_subst', 'translate_collectionSentence', 'collectionMatrix_specialize', 'zf_canonicalG_provable', 'nativeG_distinct', 'zf_nativeG_distinct', 'zf_nativeG_coincident', 'decoded_zero_equiv_top', 'zf_nativeG_decoded', 'zf_decoded_bundleG_provable']
SPECS=[('compiled', 'compiled-collection254-verification.json', 'ZFCinPA.CompiledCollection254', '23a19b6390ce8b48b92924e607f0bbdd07d14f08889892e4ba8466d95031487b', 5, 8, '78a065fe80425f362b9512ff3fa404277baf4f8e4fb96a04e7107bdc9a236aa9', '069df1a88e9f94c8ba8d2a7021ec6a50d8ed4acdf0d0a89ad2df8c551a3ba65e'), ('slots', 'model-coded-bind-two-slots-verification.json', 'ZFCinPA.ModelCodedBindTwoSlots', '34ba624f5a8b590f9168d9c8a93e34e0a162a81643d5581813fe017e0e94c0de', 8, 12, '0dfaed33a0fdd3e818520f3a03694aa3dd88404be3f7a23ae85d8f6aa0463d8d', 'ba2911e862715ca7afb493c4b65ecd43dd983d4a315473cfc6a1f985b09c35da'), ('normalization', 'model-coded-decoder-collection-normalization254-verification.json', 'ZFCinPA.ModelCodedDecoderCollectionNormalization254', '7caade6d321f2997f5fc746e7435ca9cfc59fb5c4106db61330df308587614ff', 3, 6, '888c5a4475cbf238e2b7d760f82db8125172b7c0676b68ee00f2f470b41a208f', '1854d89a2847367e0fba9e008ab52d3ccc3b951414312221ecfa5b5ba538fff4'), ('freshness', 'model-coded-decoder-freshness254-verification.json', 'ZFCinPA.ModelCodedDecoderFreshness254', '61fbed2347cdb94d1ad033b60e47c5d38e5911e2a858ea3380d08e30a6887d92', 8, 12, '62d50a4c46bbd83a32452b650ddecc311555eb024fbe7aa30f11df0057b45b83', '5500b3b3ecee902725a6e89fab4ae7247ddfda86e1c88a27d092dc1e9995e549')]
PROJECTS=['BoundedPAConsistency.TypedTemplateProofCompiler', 'BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.OmegaRecursion', 'BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCode254', 'BusyBeaver.ZFC.ArithmeticTemplates254', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.InternalOrd', 'BusyBeaver.ZFC.InternalRank', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.NamedZF', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'BusyBeaver.ZFC.ZFRank', 'FirstOrder.Calculus', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf', 'ZFCinPA.BufferedTemplateProofCompiler', 'ZFCinPA.CollectionResources254', 'ZFCinPA.CollectionTemplate254', 'ZFCinPA.CompiledCollection254', 'ZFCinPA.Instances', 'ZFCinPA.ModelCodedBindFree', 'ZFCinPA.ModelCodedBindOne', 'ZFCinPA.ModelCodedBindTwoSlots', 'ZFCinPA.ModelCodedBinderAbsorption', 'ZFCinPA.ModelCodedClosedSchemaAxioms', 'ZFCinPA.ModelCodedDecoder254', 'ZFCinPA.ModelCodedDecoderAtomicVacuity254', 'ZFCinPA.ModelCodedDecoderCircuits254', 'ZFCinPA.ModelCodedDecoderCollectionNormalization254', 'ZFCinPA.ModelCodedDecoderConstructors254', 'ZFCinPA.ModelCodedDecoderContainer254', 'ZFCinPA.ModelCodedDecoderEquality254', 'ZFCinPA.ModelCodedDecoderFalsity254', 'ZFCinPA.ModelCodedDecoderFreshness254', 'ZFCinPA.ModelCodedDecoderGeneralization254', 'ZFCinPA.ModelCodedDecoderLukasiewicz254', 'ZFCinPA.ModelCodedDecoderPropositional254', 'ZFCinPA.ModelCodedDecoderRho1_254', 'ZFCinPA.ModelCodedDecoderRho2_254', 'ZFCinPA.ModelCodedDecoderRho6_254', 'ZFCinPA.ModelCodedFreeRenaming', 'ZFCinPA.ModelCodedNamedBinderLaws', 'ZFCinPA.ModelCodedNamedLogicalNormalization254', 'ZFCinPA.ModelCodedNamedQuantifierTemplates254', 'ZFCinPA.ModelCodedOpenSchemaAxioms', 'ZFCinPA.ModelCodedProofRenaming', 'ZFCinPA.ModelCodedRenamingAxioms', 'ZFCinPA.ModelCodedRenamingBindOne', 'ZFCinPA.ModelCodedRenamingSets', 'ZFCinPA.ModelCodedSchemaAxioms', 'ZFCinPA.ModelCodedShiftCancellation', 'ZFCinPA.ModelCodedSpecialization', 'ZFCinPA.NativeZFContainers254', 'ZFCinPA.OpenSchemaTemplates', 'ZFCinPA.OpenSetTemplateCompiler', 'ZFCinPA.OpenTemplateClosure', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.SetCongruence', 'ZFCinPA.SetPlaceholderQuotient', 'ZFCinPA.SetPlaceholders', 'ZFCinPA.ZFDelta1']
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
 p.add_argument('--unused-cantor-object',type=Path,help='Optional relocation of the exact unselected inherited ff1e object; selected bf2 object stays in project-cache.')
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 S=(a.source or P/'Lean/ZFCinPA/ModelCodedDecoderCollection254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedDecoderCollection254Audit.lean').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 records=[];parent_evidence=[];parent_files=[];prior={};boundary={};source_overrides={};variants=[]
 for key,filename,module,recordhash,probes,callers,sourcehash,audithash in SPECS:
  path=(getattr(a,key+'_evidence')or P/'results'/filename).resolve();req(sha(path)==recordhash,'Wrong exact historical PASS record '+key)
  e=json.loads(path.read_text());records.append(e);parent_evidence.append(dict(key=key,path=str(path),sha256=sha(path)))
  req(e['status']=='PASS'and e['named_axiom_probes']==probes and e['callers']==callers and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong parent PASS contract '+key)
  sm=e.get('source')or{'sha256':e['sources'][0]['source_sha256']};am=e.get('audit')or{'sha256':e['sources'][0]['audit_sha256']}
  req((sm['sha256'],am['sha256'])==(sourcehash,audithash),'Wrong parent source/audit '+key)
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
  vv=e.get('inherited_shared_compiled_variants',[]);req(len(vv)==({'normalization':3,'freshness':1}.get(key,0)),'Wrong inherited variant count '+key)
  for v in vv:
   req((v['module'],v['source_sha256'],v['selected_sha256'],v['unused_recorded_sha256'])==('BusyBeaver.ZFC.ArithmeticCantor','aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84','bf2ee28833f61c6c9c44244cb22ec8932c6a3570beed1e94749b2ab1e6b9cc71','ff1e2f291d3d81940552aeb6a2a221dbfefd032005b10c9ca4d20ba4b84fb3b8'),'Wrong exact inherited Cantor pair.')
   v=dict(v)
   if a.unused_cantor_object:
    v['historical_unused_recorded_object']=v['unused_recorded_object'];v['unused_recorded_object']=str(a.unused_cantor_object.resolve())
   req(sha(v['unused_recorded_object'])==v['unused_recorded_sha256'],'Changed unused historical Cantor.');variants.append(v)
 req(len(variants)==4,'Wrong inherited numeric-parent count.')
 v=variants[0];req((prior[v['module']]['source_sha256'],prior[v['module']]['object_sha256'])==(v['source_sha256'],v['selected_sha256']),'Wrong selected Cantor identity.')
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(records[0]['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete existing Foundation namespace.')
 roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean','BoundedZFCConsistency':'SetTheory/BoundedConsistency/Lean','ZF':'SetTheory/ZF/Lean','BoundedPAConsistency':'Logic/PeanoArithmetic/BoundedConsistency/Lean'}
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
 imports=['ZFCinPA.CompiledCollection254','ZFCinPA.ModelCodedBindTwoSlots','ZFCinPA.ModelCodedDecoderCollectionNormalization254','ZFCinPA.ModelCodedDecoderFreshness254']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong direct source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS)and set(external)==set(boundary),'Wrong exact selected closure.')
 req(all(module in selected for _,_,module,*_ in SPECS),'A parent fresh object is not actually imported.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==16,'Wrong focused audit.')
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
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Actual internal ZF proof of decoded numerical G for arbitrary internal a,b,c under only c!=a/c!=b. Uses fully compiled Collection and exact typed syntax, with coincident and code-zero branches. No full bundle or PA consistency endpoint.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),parent_evidence=parent_evidence,reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(tool_direct),dependencies=deps,exact_project_import_closure=True,inherited_shared_compiled_variants=variants,all_four_parent_fresh_objects_imported=True,unused_parent_modules=sorted(set(prior)-set(selected)),before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
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
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=10,callers=16,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
