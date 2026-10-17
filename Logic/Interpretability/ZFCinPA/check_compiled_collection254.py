"""Actual internal Collection proof from a fixed source derivation and discharged axiom callbacks; no dependency build/fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.CompiledCollection254'

NAMES=['LeanProofs.ZFCinPA.CompiledCollection254.equality_cases', 'LeanProofs.ZFCinPA.CompiledCollection254.translated_equality', 'LeanProofs.ZFCinPA.CompiledCollection254.translated_axiom', 'LeanProofs.ZFCinPA.CompiledCollection254.collectionProof', 'LeanProofs.ZFCinPA.CompiledCollection254.collectionProof_isProof']
SOURCE_SHA='78a065fe80425f362b9512ff3fa404277baf4f8e4fb96a04e7107bdc9a236aa9'
AUDIT_SHA='069df1a88e9f94c8ba8d2a7021ec6a50d8ed4acdf0d0a89ad2df8c551a3ba65e'
PROJECTS=['BoundedPAConsistency.TypedTemplateProofCompiler', 'BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.OmegaRecursion', 'BusyBeaver.ZFC.InternalOrd', 'BusyBeaver.ZFC.InternalRank', 'BusyBeaver.ZFC.NamedZF', 'BusyBeaver.ZFC.ZFRank', 'FirstOrder.Calculus', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf', 'ZFCinPA.BufferedTemplateProofCompiler', 'ZFCinPA.CollectionResources254', 'ZFCinPA.CollectionTemplate254', 'ZFCinPA.Instances', 'ZFCinPA.ModelCodedBindFree', 'ZFCinPA.ModelCodedBindOne', 'ZFCinPA.ModelCodedBinderAbsorption', 'ZFCinPA.ModelCodedClosedSchemaAxioms', 'ZFCinPA.ModelCodedOpenSchemaAxioms', 'ZFCinPA.ModelCodedSchemaAxioms', 'ZFCinPA.ModelCodedShiftCancellation', 'ZFCinPA.ModelCodedSpecialization', 'ZFCinPA.NativeZFContainers254', 'ZFCinPA.OpenSchemaTemplates', 'ZFCinPA.OpenSetTemplateCompiler', 'ZFCinPA.OpenTemplateClosure', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.SetCongruence', 'ZFCinPA.SetPlaceholderQuotient', 'ZFCinPA.SetPlaceholders', 'ZFCinPA.ZFDelta1']
EXTERNALS=['Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding', 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed', 'Foundation.FirstOrder.Completeness', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Foundation.Meta.ClProver', 'Mathlib.Tactic.Ring']
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
 for key in ['schema-evidence','collection-evidence','congruence-evidence','source','audit']:p.add_argument('--'+key,type=Path)
 p.add_argument('--project-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 E=(a.schema_evidence or P/'results/open-schema-templates-verification.json').resolve()
 E2=(a.collection_evidence or P/'results/collection-template254-verification.json').resolve()
 E3=(a.congruence_evidence or P/'results/set-congruence-refresh-verification.json').resolve()
 S=(a.source or P/'Lean/ZFCinPA/CompiledCollection254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/CompiledCollection254Audit.lean').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 specs=[('schema', '7371be4b9777ad0d41a713f886120ad9c2a30aea0feb611bff5e4d0f93a48280', 5, 5, 'OpenSchemaTemplatesAudit.lean'), ('collection', '8a85acbdd23dd9633f24acc42075c883fff3a40841e78ef3cc1d915b073d7557', 7, 12, 'CollectionTemplate254Audit.lean'), ('congruence', '4369b6f41e0d0f9a59ebb69755579fb4ac2961d5710e9874d75626a697a1cc1f', 12, 14, 'SetCongruenceRefreshAudit.lean')]
 roots={'ZF': 'SetTheory/ZF/Lean', 'BoundedZFCConsistency': 'SetTheory/BoundedConsistency/Lean', 'ZFCinPA': 'Logic/Interpretability/ZFCinPA/Lean', 'BusyBeaver': 'Computability/BusyBeaver/Lean', 'FirstOrder': 'Logic/FirstOrder/Lean', 'BoundedPAConsistency': 'Logic/PeanoArithmetic/BoundedConsistency/Lean'}
 records=[];parent_files=[];prior={};boundary={}
 for (key,expected,probes,callers,auditname),path in zip(specs,[E,E2,E3]):
  req(sha(path)==expected,'Wrong exact parent record '+key)
  record=json.loads(path.read_text());records.append(record)
  req(record['status']=='PASS' and record['named_axiom_probes']==probes and record['callers']==callers and record['only_standard_axioms'] and record['all_input_provider_postchecks'] and record['all_fresh_objects_unchanged_after_audit'],'Wrong parent PASS contract '+key)
  source_rows=record.get('sources') or [dict(module='ZFCinPA.OpenSchemaTemplates',**record['source'])]
  req({q['module'] for q in source_rows}=={q['module'] for q in record['fresh_modules']},'Wrong fresh source/object set '+key)
  for q in source_rows:
   ss=R/roots[q['module'].split('.')[0]]/Path(q['module'].replace('.','/')).with_suffix('.lean')
   req(sha(ss)==q['sha256'],'Changed parent source '+q['module']);parent_files.append(ss)
   fresh=next(x for x in record['fresh_modules'] if x['module']==q['module']);req(fresh['source_sha256']==q['sha256'],'Wrong parent fresh source binding.')
  aa=P/'Lean/ZFCinPA'/auditname;req(sha(aa)==record['audit']['sha256'],'Changed parent audit '+key);parent_files.append(aa)
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
  for q in record['providers']:
   if q['module']in boundary:
    old=boundary[q['module']];req((q['source_sha256'],q['object_sha256'])==(old['source_sha256'],old['object_sha256']),'Inconsistent shared external '+q['module'])
   else:boundary[q['module']]=q
 e=records[0]
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 precursor_specs=[]
 new_sources={q['module']:R/q['path']for q in precursor_specs};fresh_visit=[]
 for q in precursor_specs:req(sha(new_sources[q['module']])==q['sha256'],'Changed fresh project precursor '+q['module'])
 selected={};external={};visiting=set()
 def visit(m):
  if m in selected or m in external or m in fresh_visit:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in new_sources:
   for n in H.lean_imports(new_sources[m].read_text()):visit(n)
   fresh_visit.append(m)
  elif m in prior:
   old=prior[m];ss=(R/roots[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected predecessor '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];root=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=root/rel.with_suffix('.lean')
   o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m)
   external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Selected source/object boundary, not whole-cache attestation.'))
  visiting.remove(m)
 imports=['ZFCinPA.CollectionTemplate254', 'ZFCinPA.OpenSchemaTemplates', 'ZFCinPA.SetCongruence']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS)and set(external)==set(EXTERNALS)and fresh_visit==[q['module']for q in precursor_specs],'Wrong exact project/fresh closure.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==NAMES and len(re.findall(r'^example\b',A.read_text(),re.M))==8,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 fresh_sources=[]
 for q in precursor_specs:
  ss0=new_sources[q['module']];snap0=snaps/Path(q['module'].replace('.','/')).with_suffix('.lean');snap0.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ss0,snap0);fresh_sources.append(dict(module=q['module'],path=str(ss0),sha256=sha(ss0),snapshot=str(snap0)))
 files=[S,A,*new_sources.values()]+[Path(q['source'])for q in list(selected.values())+list(external.values())];direct={m for f in files for m in H.lean_imports(f.read_text())if m in {'Init','Std','Lean'} or m.startswith(('Init.','Std.','Lean.'))};tool=[];toolroot=C.parent.parent/'lib/lean'
 for m in sorted(direct|{'Init','Std','Lean','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in [q for record in records for q in record.get('toolchain_providers',[])]:
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different predecessor toolchain provider.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,E2,E3,C,S,A,ss,aa,D/'lake-manifest.json',*parent_files]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs.extend(Path(q[k])for q in fresh_sources for k in ['path','snapshot'])
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Actual internal ZF Collection proof for arbitrary internal binary predicates from one fixed source derivation with every axiom callback discharged. No decoder G or PA endpoint.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=[dict(path=str(p),sha256=sha(p)) for p in [E,E2,E3]],reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,fresh_precursor_sources=fresh_sources,exact_project_import_closure=True,parent_fresh_object_imported=True,parent_evidence_scope="Actual OpenSchemaTemplates, fixed Collection template and refreshed set congruence; exact shared providers. No Atomic or Cantor import",unused_parent_boundaries=sorted(set(boundary)-set(external)),unused_parent_modules=sorted(set(prior)-set(selected)),before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
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
  fresh=[]
  for q in fresh_sources+[dict(module=MODULE,path=str(S),sha256=sha(S),snapshot=str(ss))]:
   o=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run(q['module'],Path(q['snapshot']),o);fresh.append(dict(module=q['module'],path=str(o),sha256=sha(o),source_sha256=q['sha256']))
  out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==names and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(all(sha(q['path'])==q['sha256']for q in fresh),'Changed fresh object.')
  r.update(status='PASS',fresh_modules=fresh,named_axiom_probes=5,callers=8,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
