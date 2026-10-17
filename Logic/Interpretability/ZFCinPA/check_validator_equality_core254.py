"""Check finite all-internal CProv equality and atomic congruence arguments.

Only this source and focused audit are built. Existing cached dependencies are
read-only boundaries, not a fresh/transitive whole-cache attestation.
Prepare-only performs no compiler/version query or source/audit build.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ValidatorEqualityCore254'
PREFIX='LeanProofs.ZFCinPA.ValidatorEqualityCore254.'
SOURCE_SHA='db72d9de012d6b3c2e1fbc7c283925bfbbb78bd76c9f1aa356637143b2a9e3e7'
AUDIT_SHA='2f559343a13499f38f6dc5dda8c002b416e775296e35efa5a6287641f383b709'
NAMES=['eq_refl', 'eq_symm', 'eq_trans', 'rel_left', 'rel_right', 'eq_left', 'eq_right', 'rel_congr', 'eq_congr']
PARENT_SOURCE='4afb9947d05cf713b74c16cb8162af5b0e6c03461ed87e21cbdf1da3303ea2f1'
PARENT_AUDIT='e66efc5fed7547b51ec97225e6d6ae92b4d91be68a8a42fdc26c235eac339e6b'
PARENT_OBJECT='23aec68314992d3b63c020f2c4abb3daf3cad038e663dbdfc663fb792ed68c0f'
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
 p.add_argument('--quantifier-evidence',type=Path);p.add_argument('--project-cache',type=Path)
 p.add_argument('--source',type=Path)
 p.add_argument('--audit',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve()
 S=(a.source or R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEqualityCore254.lean').resolve()
 A=(a.audit or R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEqualityCore254Audit.lean').resolve()
 E=(a.quantifier_evidence or R/'Logic/Interpretability/ZFCinPA/results/validator-quantifier-core254-verification.json').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 req(sha(E)=='a5d44ee88abad04bf5a3a6f6e9a470e2c1b72970cfa5063ea3129dfc300240ca','Wrong exact successful Quantifier record.')
 e=json.loads(E.read_text())
 req(sha(helper)==e['before'][str(helper)],'Different exact parent discovery helper.')
 C=(a.lean or Path(e['compiler']['path'])).expanduser().resolve();version=e['compiler']['version']
 req(sha(C)==e['compiler']['sha256'],'Different compiler binary.')
 if not a.prepare_only:req(subprocess.check_output([str(C),'--version'],text=True).strip()==version,'Different observed compiler version.')
 libs,deps=H.dependency_libraries(D,a.library_path)
 req(e['status']=='PASS'and e['named_axiom_probes']==25 and e['callers']==18 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Need actual Quantifier25/18 PASS.')
 req((e['source']['sha256'],e['audit']['sha256'])==(PARENT_SOURCE,PARENT_AUDIT),'Wrong exact parent source/audit.')
 f,=e['fresh_modules'];req((f['module'],f['source_sha256'],f['sha256'])==('ZFCinPA.ValidatorQuantifierCore254',PARENT_SOURCE,PARENT_OBJECT),'Wrong exact parent fresh object.')
 req((sha(C),version)==(e['compiler']['sha256'],e['compiler']['version']),'Different compiler.')
 for name in ['Foundation','Mathlib']:req(deps[name]['pin']==e['dependencies'][name]['pin']and deps[name]['tracked_clean']and e['dependencies'][name]['tracked_clean'],'Wrong dependency pin/clean state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Wrong manifest.')
 req(set(deps['providers'])==set(e['dependencies']['providers']),'Wrong base provider set.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Wrong base provider '+m)
 prior={q['module']:q for q in e['reused_modules']};prior[f['module']]=dict(module=f['module'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
 boundary={q['module']:q for q in e['providers']};selected={};external={};visiting=set();tools=set()
 roots={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BusyBeaver':'Computability/BusyBeaver/Lean','FirstOrder':'Logic/FirstOrder/Lean'}
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
 imports=['ZFCinPA.ValidatorQuantifierCore254']
 req(H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[MODULE],'Wrong source/audit imports.')
 for m in imports:visit(m)
 for m in deps['providers']:visit(m)
 direct_external_imports=sorted(external)
 # Seq is the explicitly retained parent history/iteration anchor, not a direct DFS import.
 visit('Foundation.FirstOrder.Arithmetic.HFS.Seq')
 req(set(selected)==set(prior)and len(selected)==21 and set(external)==set(boundary)and len(external)==4,'Wrong exact21-project/4-boundary closure.')
 parentAudit=R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorQuantifierCore254Audit.lean'
 req(sha(parentAudit)==PARENT_AUDIT,'Changed maintained parent audit.')
 expected=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);callers=len(re.findall(r'^example\b',A.read_text(),re.M))
 req(expected==[PREFIX+n for n in NAMES]and len(expected)==9 and callers==12,'Wrong9/12 audit contract.')
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
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Finite all-internal CProv reflexivity, symmetry, transitivity and equality/membership congruence, deriving the fresh reflexivity witness from x+1 and both original atomic-vacuity gates. No represented environment/alpha induction, formula/proof compiler, axiom transport, reverse consistency or binary endpoint.',quantifier_evidence=dict(path=str(E),sha256=sha(E)),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),compiler=dict(path=str(C),sha256=sha(C),version=version),reused_modules=list(selected.values()),providers=list(external.values()),direct_external_imports=direct_external_imports,iteration_anchor_modules=['Foundation.FirstOrder.Arithmetic.HFS.Seq'],toolchain_providers=tool,dependencies=deps,exact_project_import_closure=True,parent_fresh_object_imported=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_limit_mib=4096,per_command_timeout_seconds=120,global_option_overrides=[],compiler_version_query_performed=not a.prepare_only,dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(p):sha(p)for p in inputs};req(before==after,'Changed immutable input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(x/rel for x in [cache,*libs,toolroot]if(x/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic()
  try:
   cp=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True,timeout=120);out=cp.stdout+cp.stderr;code=cp.returncode;timeout=False
  except subprocess.TimeoutExpired as ex:
   def text(v):return v.decode(errors='replace')if isinstance(v,bytes)else(v or'')
   out=text(ex.stdout)+text(ex.stderr);code=None;timeout=True
  (W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=code,timed_out=timeout,output=out));save()
  req(not timeout,'Compiler timeout; FAIL retained.')
  req(code==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out)
  print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run('source',ss,o);oh=sha(o)
  r.update(source_passed=True,fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],fresh_object_sha256_before_audit=oh);save()
  req(sha(o)==oh,'Changed fresh source object before audit.')
  out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==expected and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.')
  post();req(sha(o)==oh,'Changed fresh object.')
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=9,callers=12,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
