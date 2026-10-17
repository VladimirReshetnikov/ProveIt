"""Buffered compilation of fixed ordinary proof templates; no dependency build/fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.BufferedTemplateProofCompiler'
PREFIX='LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.'
NAMES=['translateSequent_insert','BufferedTranslation.sequent_shift','BufferedTranslation.closed_buffer','bufferBound','compileDerivation','compileProof','compileProof_isProof']
SOURCE_SHA='56a9d1ef8e7169207576dbe3f806cf4f21fe95bd4082300b3acc70d7ade320be'
AUDIT_SHA='37521def4f52ab280f4628195127216fdd7fd0ae10b1408f597d8a0dbd7de380'
PROJECTS=['ZFCinPA.ModelCodedShiftCancellation', 'ZFCinPA.Instances', 'ZFCinPA.ModelCodedBindFree', 'ZFCinPA.ModelCodedBindOne', 'ZFCinPA.ModelCodedBinderAbsorption', 'ZFCinPA.ModelCodedClosedSchemaAxioms', 'ZFCinPA.ModelCodedSchemaAxioms', 'ZFCinPA.ModelCodedSpecialization', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.ZFDelta1']
EXTERNALS=['Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding', 'Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Mathlib.Tactic.Ring']
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
 for key in ['shift-evidence','source','audit','shift-source','shift-audit']:p.add_argument('--'+key,type=Path)
 p.add_argument('--project-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 E=(a.shift_evidence or P/'results/model-coded-shift-cancellation-verification.json').resolve()
 S=(a.source or P/'Lean/ZFCinPA/BufferedTemplateProofCompiler.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/BufferedTemplateProofCompilerAudit.lean').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 req(sha(E)=='8c9cad55fc156c994c9da2186279d34682fa474fb509ea123268455cdbc44a15','Wrong exact shift-cancellation evidence.')
 specs=[('shift',E,'ZFCinPA.ModelCodedShiftCancellation',6,9,'ab8b72fb2516e95c97ca6a5d26f73a4ae9f721941c15fc9c3c49f5fbf4582c06','c1a49827aef000737fbd582b8747c2de7b0ef4f6278992bf5ad7a204c788cc26')]
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
 boundary['Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding']={'module': 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding', 'source_sha256': '85eedc601aa9912320ccb92898b1c12fa3c51dffae81a44ce3666d5efd472998', 'object_sha256': 'dc6ca691ab138cb97276404acc7e6cd79c4ff018d5b153d243e607a4ecdbdcfd', 'scope': 'Additional direct source/object Coding boundary; no dependency rebuild or whole-cache attestation.'}
 e,=records
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 selected={};external={};visiting=set();roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean'}
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];source_override={'ZFCinPA.ModelCodedShiftCancellation':a.shift_source}.get(m);ss=(source_override or R/roots[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected predecessor '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];root=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=root/rel.with_suffix('.lean')
   o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m)
   external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Selected source/object boundary, not whole-cache attestation.'))
  visiting.remove(m)
 imports=['ZFCinPA.ModelCodedShiftCancellation','Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS)and set(external)==set(EXTERNALS),'Wrong exact project closure.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==9,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 files=[S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())];direct={m for f in files for m in H.lean_imports(f.read_text())if m.startswith('Lean.')};tool=[];toolroot=C.parent.parent/'lib/lean'
 for m in sorted(direct|{'Init','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in [q for record in records for q in record.get('toolchain_providers',[])]:
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different predecessor toolchain provider.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,D/'lake-manifest.json',*parent_files]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Logical finite-buffer compiler for fixed ordinary derivations. Explicit translation laws and axiom-proof callbacks; no concrete open-predicate translation or Collection theorem.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),shift_evidence=dict(path=str(E),sha256=sha(E)),reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,exact_project_import_closure=True,parent_fresh_object_imported=True,parent_evidence_scope="Actual ShiftCancellation fresh object plus eleven syntax ancestors; no Atomic or Cantor import",unused_parent_boundaries=sorted(set(boundary)-set(external)),unused_parent_modules=sorted(set(prior)-set(selected)),before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
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
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=7,callers=9,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
