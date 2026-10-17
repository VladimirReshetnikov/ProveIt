"""Check the narrow all-internal CProv interface against exact checked Constructors.

Only this source and focused audit are built. Existing cached dependencies are
read-only boundaries, not a fresh/transitive whole-cache attestation.
Prepare-only queries the compiler version and performs no source/audit build.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ValidatorProvability254'
PREFIX='LeanProofs.ZFCinPA.ValidatorProvability254.'
SOURCE_SHA='372a7fbd58fb5d018951e3e23dc308062ad02546279620e1d67fb3d06e7845b6'
AUDIT_SHA='db60655f244259ebe9f3049211633f4d5d01ed49d81413d9c4d68a0e8e28a56b'
NAMES=['cProv_defined', 'cProv_definable', 'cProv_truth', 'cProv_mp', 'cProv_gen', 'cProv_rho1', 'cProv_rho2', 'cProv_rho3', 'cProv_rho4', 'cProv_rho5', 'cProv_rho6', 'cProv_rho7', 'cProv_rho8', 'cProv_bundle', 'cProv_implicational', 'cProv_k', 'cProv_s', 'cProv_peirce', 'cProv_composition', 'cProv_ex_falso', 'cProv_classical', 'cProv_nat_iff']
PARENT_SOURCE='34d33aeb05b4b37a29659aa3d6e86281783fab70574a8352eded4560b6dfb875'
PARENT_AUDIT='8949c5527726bf5eeed70ee736db2d1977b7c36d4a7fb2ab493479914d0eb095'
PARENT_OBJECT='4f388e3d57d5bf90c58edb5f3a6f4e82b04ad78b45708ca34f0b2b787e18d1f0'
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
 p.add_argument('--constructors-evidence',type=Path);p.add_argument('--project-cache',type=Path)
 p.add_argument('--source',type=Path)
 p.add_argument('--audit',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve()
 S=(a.source or R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorProvability254.lean').resolve()
 A=(a.audit or R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorProvability254Audit.lean').resolve()
 E=(a.constructors_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-proof-constructors254-verification.json').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 e=json.loads(E.read_text())
 req(e['status']=='PASS'and e['named_axiom_probes']==17 and e['callers']==18 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Need actual Constructors17/18 PASS.')
 req((e['source']['sha256'],e['audit']['sha256'])==(PARENT_SOURCE,PARENT_AUDIT),'Wrong exact parent source/audit.')
 f,=e['fresh_modules'];req((f['module'],f['source_sha256'],f['sha256'])==('BusyBeaver.ZFC.ArithmeticProofConstructors254',PARENT_SOURCE,PARENT_OBJECT),'Wrong exact parent fresh object.')
 req((sha(C),version)==(e['compiler']['sha256'],e['compiler']['version']),'Different compiler.')
 for name in ['Foundation','Mathlib']:req(deps[name]['pin']==e['dependencies'][name]['pin']and deps[name]['tracked_clean']and e['dependencies'][name]['tracked_clean'],'Wrong dependency pin/clean state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Wrong manifest.')
 req(set(deps['providers'])==set(e['dependencies']['providers']),'Wrong base provider set.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Wrong base provider '+m)
 prior={q['module']:q for q in e['reused_modules']};prior[f['module']]=dict(module=f['module'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
 boundary={q['module']:q for q in e['providers']};selected={};external={};visiting=set();tools=set()
 roots={'BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean'}
 def visit(m):
  if m in selected or m in external:return
  if m.split('.')[0]in ['Lean','Std','Init']:tools.add(m);return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];ss=(R/roots[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=(a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])).resolve()
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected project '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];dr=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=dr/rel.with_suffix('.lean')
   o=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
   req(o is not None and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed actual external boundary '+m)
   external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope='Exact source/object cached import boundary; not whole namespace attestation.')
  visiting.remove(m)
 imports=['BusyBeaver.ZFC.ArithmeticProofConstructors254']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 direct_external_imports=sorted(external)
 # Seq is the explicitly retained parent history/iteration anchor, not a direct DFS import.
 visit('Foundation.FirstOrder.Arithmetic.HFS.Seq')
 req(set(selected)==set(prior)and len(selected)==19 and set(external)==set(boundary)and len(external)==4,'Wrong exact19-project/4-boundary closure.')
 parentAudit=R/'Computability/BusyBeaver/Research/ZFC/arithmetic_proof_constructors254_audit.lean'
 req(sha(parentAudit)==PARENT_AUDIT,'Changed maintained parent audit.')
 expected=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);callers=len(re.findall(r'^example\b',A.read_text(),re.M))
 req(expected==[PREFIX+n for n in NAMES]and len(expected)==22 and callers==16,'Wrong22/16 audit contract.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir()
 for q in selected.values():
  dst=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 files=[S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]
 for pth in files:tools.update(m for m in H.lean_imports(pth.read_text())if m.split('.')[0]in ['Lean','Std','Init'])
 tools.update({'Init','Lean.Elab.Tactic.Omega'});toolroot=C.parent.parent/'lib/lean';tool=[]
 for m in sorted(tools):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((x/rel for x in [cache,*libs,toolroot]if(x/rel).is_file()),None)
  req(o is not None and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,parentAudit,D/'lake-manifest.json']+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(p.resolve()for p in inputs));before={str(p):sha(p)for p in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Fixed Sigma1 CProv predicate and actual all-internal twelve-rule closure, with polymorphic Kalmar.Classical wim1 interface. No internal formula/proof encoder, reverse consistency or binary endpoint.',constructors_evidence=dict(path=str(E),sha256=sha(E)),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),compiler=dict(path=str(C),sha256=sha(C),version=version),reused_modules=list(selected.values()),providers=list(external.values()),direct_external_imports=direct_external_imports,iteration_anchor_modules=['Foundation.FirstOrder.Arithmetic.HFS.Seq'],toolchain_providers=tool,dependencies=deps,exact_project_import_closure=True,parent_fresh_object_imported=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_limit_mib=4096,dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(p):sha(p)for p in inputs};req(before==after,'Changed immutable input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(x/rel for x in [cache,*libs,toolroot]if(x/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save();req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run('source',ss,o);oh=sha(o);out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==expected and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.')
  post();req(sha(o)==oh,'Changed fresh object.')
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=22,callers=16,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
