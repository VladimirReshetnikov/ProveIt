"""Narrow finite named logical normalization; no dependency build/fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedNamedLogicalNormalization254'
PREFIX='LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.'
NAMES=['namedExists_as_negAll', 'relativeConj_equiv', 'relativeConj_intro', 'relativeConj_left', 'relativeConj_right', 'namedExists_equiv', 'relativeExists_equiv']
SOURCE_SHA='42a8a919d0c77fa7ac00f0c29fc45450afe49e69a28ab4a7923f74d791bd30da'
AUDIT_SHA='77fc039fcac043dec64b8e9762b6371fb3974fd7132b248f1e892263cbc45beb'
PROJECTS=['BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCode254', 'BusyBeaver.ZFC.ArithmeticTemplates254', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'FirstOrder.Fol', 'ZFCinPA.Instances', 'ZFCinPA.ModelCodedBindFree', 'ZFCinPA.ModelCodedBindOne', 'ZFCinPA.ModelCodedBinderAbsorption', 'ZFCinPA.ModelCodedClosedSchemaAxioms', 'ZFCinPA.ModelCodedDecoder254', 'ZFCinPA.ModelCodedDecoderConstructors254', 'ZFCinPA.ModelCodedDecoderEquality254', 'ZFCinPA.ModelCodedDecoderFalsity254', 'ZFCinPA.ModelCodedDecoderGeneralization254', 'ZFCinPA.ModelCodedDecoderLukasiewicz254', 'ZFCinPA.ModelCodedDecoderPropositional254', 'ZFCinPA.ModelCodedDecoderRho1_254', 'ZFCinPA.ModelCodedDecoderRho2_254', 'ZFCinPA.ModelCodedDecoderRho6_254', 'ZFCinPA.ModelCodedFreeRenaming', 'ZFCinPA.ModelCodedNamedBinderLaws', 'ZFCinPA.ModelCodedNamedQuantifierTemplates254', 'ZFCinPA.ModelCodedProofRenaming', 'ZFCinPA.ModelCodedRenamingAxioms', 'ZFCinPA.ModelCodedRenamingBindOne', 'ZFCinPA.ModelCodedRenamingSets', 'ZFCinPA.ModelCodedSchemaAxioms', 'ZFCinPA.ModelCodedSpecialization', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.ZFDelta1']
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
 for key in ['rho1-evidence','source','audit','rho1-source','rho1-audit']:p.add_argument('--'+key,type=Path)
 p.add_argument('--project-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 E=(a.rho1_evidence or P/'results/model-coded-decoder-rho1-254-verification.json').resolve()
 S=(a.source or P/'Lean/ZFCinPA/ModelCodedNamedLogicalNormalization254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedNamedLogicalNormalization254Audit.lean').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 specs=[('rho1',E,'ZFCinPA.ModelCodedDecoderRho1_254',10,16,'8a962f910ae4795838e5607ee43b10ae1037b75667d76dcf1f3998a231ff8314','6242ab516f6bc7ca20dd0deccd21cd138dec9b99f8042895a421fb9c1b0c62f7')]
 records=[];parent_files=[];prior={};boundary={}
 for key,path,module,probes,callers,sourcehash,audithash in specs:
  record=json.loads(path.read_text());records.append(record)
  req(record['status']=='PASS'and record['named_axiom_probes']==probes and record['callers']==callers and record['only_standard_axioms']and record['all_input_provider_postchecks']and record['all_fresh_objects_unchanged_after_audit'],'Wrong parent PASS contract '+key)
  req('source' in record and 'audit' in record,'Wrong scalar parent shape.');sh=record['source']['sha256'];ah=record['audit']['sha256']
  req((sh,ah)==(sourcehash,audithash),'Wrong frozen parent source/audit '+key)
  req(len(record['fresh_modules'])==1 and record['fresh_modules'][0]['module']==module and record['fresh_modules'][0]['source_sha256']==sourcehash,'Wrong parent fresh object metadata '+key)
  ss=(getattr(a,key+'_source')or P/'Lean'/Path(module.replace('.','/')).with_suffix('.lean')).resolve();aa=(getattr(a,key+'_audit')or P/'Lean/ZFCinPA'/(module.split('.')[-1]+'Audit.lean')).resolve()
  req(sha(ss)==sourcehash and sha(aa)==audithash,'Changed parent source/audit '+key);parent_files.extend([ss,aa])
  req(sha(C)==record['compiler']['sha256']and version==record['compiler']['version'],'Different compiler '+key)
  if records[:-1]:req(record['compiler']==records[0]['compiler'],'Different recorded parent compiler identity.')
  for dep in ['Foundation','Mathlib']:req(record['dependencies'][dep]['pin']==deps[dep]['pin']and record['dependencies'][dep]['tracked_clean']and deps[dep]['tracked_clean'],'Different dependency pin/state '+key)
  req(record['dependencies']['lake_manifest_sha256']==deps['lake_manifest_sha256'],'Different manifest '+key)
  for m,q in deps['providers'].items():req(q['sha256']==record['dependencies']['providers'][m]['sha256'],'Different base provider '+key)
  rows=record['reused_modules']+[dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256'])for q in record['fresh_modules']]
  for q in rows:
   if q['module']in prior:
    old=prior[q['module']];req((q['source_sha256'],q['object_sha256'])==(old['source_sha256'],old['object_sha256']),'Inconsistent shared project '+q['module'])
   else:prior[q['module']]=q
  if boundary:req(set(boundary)=={q['module']for q in record['providers']},'Different parent boundary set '+key)
  for q in record['providers']:
   if q['module']in boundary:
    old=boundary[q['module']];req((q['source_sha256'],q['object_sha256'])==(old['source_sha256'],old['object_sha256']),'Inconsistent shared external '+q['module'])
   else:boundary[q['module']]=q
 e,=records
 variants=e['inherited_shared_compiled_variants'];req(len(variants)==1,'Wrong inherited Cantor variant records.');v=variants[0]
 req((v['module'],v['source_sha256'],v['selected_sha256'],v['unused_recorded_sha256'])==('BusyBeaver.ZFC.ArithmeticCantor','aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84','bf2ee28833f61c6c9c44244cb22ec8932c6a3570beed1e94749b2ab1e6b9cc71','ff1e2f291d3d81940552aeb6a2a221dbfefd032005b10c9ca4d20ba4b84fb3b8'),'Wrong frozen inherited Cantor pair.')
 req(prior[v['module']]['source_sha256']==v['source_sha256']and prior[v['module']]['object_sha256']==v['selected_sha256']and sha(v['unused_recorded_object'])==v['unused_recorded_sha256'],'Changed inherited variant identity.')
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 selected={};external={};visiting=set();roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean'}
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];source_override={'ZFCinPA.ModelCodedDecoderRho1_254':a.rho1_source}.get(m);ss=(source_override or R/roots[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected predecessor '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];root=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=root/rel.with_suffix('.lean')
   o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m)
   external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Selected source/object boundary, not whole-cache attestation.'))
  visiting.remove(m)
 imports=['ZFCinPA.ModelCodedDecoderRho1_254']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS)and set(external)==set(boundary),'Wrong exact project closure.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==10,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 files=[S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())];direct={m for f in files for m in H.lean_imports(f.read_text())if m.startswith('Lean.')};tool=[];toolroot=C.parent.parent/'lib/lean'
 for m in sorted(direct|{'Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in [q for record in records for q in record.get('toolchain_providers',[])]:
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different predecessor toolchain provider.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,D/'lake-manifest.json',Path(v['unused_recorded_object']),*parent_files]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Finite implication/Bottom conjunction and named-existential normalization at arbitrary internal matrices/labels; explicit target GEN only for named equivalence. No container/GIC or full bundle/PA proof.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),rho1_evidence=dict(path=str(E),sha256=sha(E)),reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,exact_project_import_closure=True,inherited_shared_compiled_variants=variants,parent_fresh_object_imported=True,unused_parent_modules=sorted(set(prior)-set(selected)),before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider.')
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)];t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save();req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,o);oh=sha(o);out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==names and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(sha(o)==oh,'Changed fresh object.')
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=7,callers=10,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
