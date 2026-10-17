"""Narrow one-source one-variable binding traversal check; no dependency build or fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedBindOne';PREFIX='LeanProofs.ZFCinPA.ModelCodedBindOne.'
NAMES=['termBindOneAt_defined', 'termBindOneVecAt_defined', 'bindOneAt_defined', 'termBindOneAt_bvar', 'termBindOneAt_chosen', 'termBindOneAt_other', 'termBindOneAt_isSemiterm', 'termBindOneVecAt_isSemiterm', 'bindOneAt_isSemiformula', 'termBindOneAt_inverse', 'termBindOneVecAt_inverse', 'bindOneAt_inverse', 'namedAll_defined', 'namedAll_isFormula', 'bindOneAt_open']
PROJECTS={'ZFCinPA.Instances','ZFCinPA.SchemaClosure','ZFCinPA.SeparationDelta1','ZFCinPA.ReplacementDelta1','ZFCinPA.ZFDelta1','ZFCinPA.ModelCodedSchemaAxioms','ZFCinPA.ModelCodedBindFree','ZFCinPA.ModelCodedClosedSchemaAxioms','ZFCinPA.ModelCodedSpecialization'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
SOURCE_SHA256='78f5858a715e74bca2af835ec990e33775f588219ef7f30b217825acbffd6785'
AUDIT_SHA256='29467fe36a55a048fb04d136ec59926b9b8fd02ef79883d9912c129ac5c825da'
def default_repo():
 for q in Path(__file__).resolve().parents:
  if(q/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return q
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo());p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 for key in ['specialization-evidence','source','audit']:p.add_argument('--'+key,type=Path)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--specialization-cache','--closed-cache',dest='closed_cache',type=Path,help='Optional consolidated cache with all nine exact predecessor objects.')
 p.add_argument('--namespace-cache',type=Path,help='Optional cache root containing the complete Foundation namespace mirror.')
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.');R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';E=(a.specialization_evidence or P/'results/model-coded-specialization-verification.json').resolve();S=(a.source or P/'Lean/ZFCinPA/ModelCodedBindOne.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedBindOneAudit.lean').resolve();W=a.output.resolve()
 req(sha(S)==SOURCE_SHA256 and sha(A)==AUDIT_SHA256,'Wrong frozen source/audit.')
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H);C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);e=json.loads(E.read_text())
 req(e['status']=='PASS'and e['named_axiom_probes']==14 and e['callers']==16 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong predecessor contract.')
 req(e['source']['sha256']=='ae18d5c05167e4fbbf9e5bfadd6d807439140ec07031af22dc5198e4fc26ac38'and e['audit']['sha256']=='e012d98176c6b720b4b2c0e4c83f354ef3b9f3a3dd2fb22c4e6a0eea3acb0cd8','Wrong predecessor source/audit.')
 req(sha(C)==e['compiler']['sha256']and version==e['compiler']['version'],'Different compiler.')
 for dep in ['Foundation','Mathlib']:req(deps[dep]['pin']==e['dependencies'][dep]['pin']and deps[dep]['tracked_clean']and e['dependencies'][dep]['tracked_clean'],'Different dependency pin/state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Different manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Different base provider.')
 prior={q['module']:q for q in e['reused_modules']};new=e['fresh_modules'][0];req(new['module']=='ZFCinPA.ModelCodedSpecialization'and new['source_sha256']==e['source']['sha256'],'Wrong predecessor fresh module.');prior[new['module']]=dict(module=new['module'],source_sha256=new['source_sha256'],object=new['path'],object_sha256=new['sha256'])
 boundary={q['module']:q for q in e['providers']};selected={};external={};visiting=set()
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];ss=R/'Logic/Interpretability/ZFCinPA/Lean'/rel.with_suffix('.lean');o=a.closed_cache/rel.with_suffix('.olean')if a.closed_cache else Path(old['object']);req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected predecessor '+m);selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];dp=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=dp/rel.with_suffix('.lean');o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None);req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m);external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Recorded source/object boundary; no whole-cache attestation.'))
  visiting.remove(m)
 req(H.lean_imports(S.read_text())==['ZFCinPA.ModelCodedSpecialization'],'Wrong new imports.');req(H.lean_imports(A.read_text())==[MODULE],'Wrong audit imports.')
 visit('ZFCinPA.ModelCodedSpecialization')
 for m in deps['providers']:visit(m)
 req(set(selected)==PROJECTS,'Wrong exact project closure.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==19,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';(cache/'ZFCinPA').mkdir(parents=True);(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/'ZFCinPA/ModelCodedBindOne.lean';ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 toolroot=C.parent.parent/'lib/lean';tool=[];direct={m for f in [S,A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]for m in H.lean_imports(f.read_text())if m.startswith('Lean.')}
 for m in sorted(direct|{'Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None);req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in e.get('toolchain_providers',[]):
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different predecessor toolchain object.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,D/'lake-manifest.json']+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']];inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-internal binding of one free label with arbitrary-depth opening inverse; no numeric decoder or GEN proof transport.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=dict(path=str(E),sha256=sha(E)),reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,exact_project_import_closure=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
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
  o=cache/'ZFCinPA/ModelCodedBindOne.olean';run('source',ss,o);oh=sha(o);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);req([n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(sha(o)==oh,'Changed fresh object.');r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=15,callers=19,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
