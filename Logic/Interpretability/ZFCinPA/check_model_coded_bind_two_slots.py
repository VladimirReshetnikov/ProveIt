"""Guarded all-internal two-slot reindexing; one fresh module, no dependency build/fetch."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
STAGES = [{'label': 'syntax', 'module': 'ZFCinPA.ModelCodedBindTwoSlots', 'source_sha256': '0dfaed33a0fdd3e818520f3a03694aa3dd88404be3f7a23ae85d8f6aa0463d8d', 'audit_sha256': 'ba2911e862715ca7afb493c4b65ecd43dd983d4a315473cfc6a1f985b09c35da', 'names': ['LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_defined', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_zero', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_succ', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_isSemitermVec', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.twoSlotVec_spec', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.termBindTwo_reindex', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.termBindTwoVec_reindex', 'LeanProofs.ZFCinPA.ModelCodedBindTwoSlots.bindTwo_reindex'], 'callers': 12}]
PROJECTS={'ZFCinPA.Instances','ZFCinPA.SchemaClosure','ZFCinPA.SeparationDelta1',
 'ZFCinPA.ReplacementDelta1','ZFCinPA.ZFDelta1','ZFCinPA.ModelCodedSchemaAxioms',
 'ZFCinPA.ModelCodedBindFree','ZFCinPA.ModelCodedClosedSchemaAxioms',
 'ZFCinPA.ModelCodedSpecialization','ZFCinPA.ModelCodedBindOne'}
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
 p.add_argument('--bind-one-evidence',type=Path);p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
 p.add_argument('--bind-one-cache',type=Path)
 p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--through',choices=[x['label']for x in STAGES],default='syntax')
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--lean',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';E=(a.bind_one_evidence or P/'results/model-coded-bind-one-verification.json').resolve();W=a.output.resolve()
 req(sha(E)=='ba5f861549f2a15126f53eec9ea8b083ebb6faaf22ada9c08d9aa3b4150d1ed3','Wrong exact BindOne PASS evidence.')
 stage=[dict(STAGES[0],source=str((a.source or P/'Lean/ZFCinPA/ModelCodedBindTwoSlots.lean').resolve()),audit=str((a.audit or P/'Lean/ZFCinPA/ModelCodedBindTwoSlotsAudit.lean').resolve()))]
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),
     'Fresh external output required.')
 for x in stage:
  req(sha(x['source'])==x['source_sha256']and sha(x['audit'])==x['audit_sha256'],'Wrong frozen source/audit '+x['label'])
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 sp=importlib.util.spec_from_file_location('helpers',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);e=json.loads(E.read_text())
 req(e['status']=='PASS'and e['named_axiom_probes']==15 and e['callers']==19 and e['only_standard_axioms']
     and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong BindOne contract.')
 req(e['source']['sha256']=='78f5858a715e74bca2af835ec990e33775f588219ef7f30b217825acbffd6785'
     and e['audit']['sha256']=='29467fe36a55a048fb04d136ec59926b9b8fd02ef79883d9912c129ac5c825da','Wrong BindOne source/audit.')
 req(sha(C)==e['compiler']['sha256']and version==e['compiler']['version'],'Different compiler.')
 for dep in ['Foundation','Mathlib']:
  req(deps[dep]['pin']==e['dependencies'][dep]['pin']and deps[dep]['tracked_clean']and e['dependencies'][dep]['tracked_clean'],'Different dependency pin/state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Different manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Different base provider.')
 prior={q['module']:q for q in e['reused_modules']}
 new=e['fresh_modules'][0]
 req(len(e['fresh_modules'])==1 and new['module']=='ZFCinPA.ModelCodedBindOne'and new['source_sha256']==e['source']['sha256']and new['sha256']=='c80e2be803b838d943eaec9051b93b0eaa9a2f34470c60f8920821fb21a75eca','Wrong exact BindOne object.')
 parent_audit=P/'Lean/ZFCinPA/ModelCodedBindOneAudit.lean';req(sha(parent_audit)==e['audit']['sha256'],'Changed current BindOne audit.')
 prior[new['module']]=dict(module=new['module'],source_sha256=new['source_sha256'],object=new['path'],object_sha256=new['sha256'])
 boundary={q['module']:q for q in e['providers']};selected={};external={};visiting=set()
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve()
 req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 def visit(m):
  if m in selected or m in external:return
  req(m not in visiting,'Import cycle.');visiting.add(m);rel=Path(m.replace('.','/'))
  if m in prior:
   old=prior[m];ss=R/'Logic/Interpretability/ZFCinPA/Lean'/rel.with_suffix('.lean')
   o=a.bind_one_cache/rel.with_suffix('.olean')if a.bind_one_cache else Path(old['object'])
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected predecessor '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m]
   dp=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=dp/rel.with_suffix('.lean')
   o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m)
   external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Recorded source/object boundary, not whole-cache attestation.'))
  visiting.remove(m)
 newnames=set()
 for x in stage:
  imported=H.lean_imports(Path(x['source']).read_text())
  expected=['ZFCinPA.ModelCodedBindOne']if x['label']=='syntax'else['ZFCinPA.ModelCodedFreeRenaming']
  req(imported==expected,'Wrong new imports '+x['label'])
  for m in imported:
   if m not in newnames:visit(m)
  req(H.lean_imports(Path(x['audit']).read_text())==[x['module']],'Wrong audit imports.')
  req(re.findall(r'^#print axioms (\S+)$',Path(x['audit']).read_text(),re.M)==x['names']
      and len(re.findall(r'^example\b',Path(x['audit']).read_text(),re.M))==x['callers'],'Wrong focused audit '+x['label'])
  newnames.add(x['module'])
 for m in deps['providers']:visit(m)
 req(set(selected)==PROJECTS,'Wrong exact project closure.')
 req(set(external)=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Foundation.FirstOrder.SetTheory.Basic.Axioms'},'Wrong exact external boundaries.')
 W.mkdir(parents=True);cache=W/'cache';(cache/'ZFCinPA').mkdir(parents=True)
 (cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.symlink_to(q['object'])
 snaps=W/'sources';snapshots=[]
 for x in stage:
  ss=snaps/Path(x['module'].replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True,exist_ok=True)
  aa=snaps/(x['label'].title()+'Audit.lean');shutil.copyfile(x['source'],ss);shutil.copyfile(x['audit'],aa)
  snapshots.append(dict(**x,source_snapshot=str(ss),audit_snapshot=str(aa)))
 toolroot=C.parent.parent/'lib/lean';tool=[]
 sourcefiles=[Path(x[k])for x in stage for k in ['source','audit']]+[Path(q['source'])for q in list(selected.values())+list(external.values())]
 direct={m for f in sourcefiles for m in H.lean_imports(f.read_text())if m in {'Init','Std','Lean'}or m.startswith(('Init.','Std.','Lean.'))}
 for m in sorted(direct|{'Init','Std','Lean','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel
  o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in e.get('toolchain_providers',[]):
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different predecessor toolchain object.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,C,D/'lake-manifest.json',parent_audit]+sourcefiles
 inputs += [Path(x[k])for x in snapshots for k in ['source_snapshot','audit_snapshot']]
 inputs += [Path(q['object'])for q in list(selected.values())+list(external.values())]
 inputs += [Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-internal two-slot reindexing at arbitrary depths and target indices, with distinct selected labels; fixed total Sigma1 vector and Pi1 syntax induction. No native-G proof or PA endpoint.',through=a.through,
  compiler=dict(path=str(C),sha256=sha(C),version=version),sources=snapshots,
  provider_evidence=dict(path=str(E),sha256=sha(E)),reused_modules=list(selected.values()),providers=list(external.values()),
  toolchain_providers=tool,actual_direct_tool_imports=sorted(direct),dependencies=deps,exact_project_import_closure=True,
  before=before,commands=[],fresh_modules=[],completed_checkpoints=[],LEAN_PATH=env['LEAN_PATH'],
  namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean')
   o=next(d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file())
   req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed first provider.')
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.')
  r['all_input_provider_postchecks']=True
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)]
  t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True)
  out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out)
  r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save()
  req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out)
  print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 try:
  for x in snapshots:
   o=cache/Path(x['module'].replace('.','/')).with_suffix('.olean')
   run(x['label']+'-source',Path(x['source_snapshot']),o);oh=sha(o)
   out=run(x['label']+'-audit',Path(x['audit_snapshot']))
   reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
   req([n for n,_ in reports]==x['names']and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports '+x['label'])
   req(sha(o)==oh,'Changed fresh object after audit.')
   r['fresh_modules'].append(dict(module=x['module'],path=str(o),sha256=oh,source_sha256=x['source_sha256']))
   r['completed_checkpoints'].append(dict(label=x['label'],named_axiom_probes=len(x['names']),callers=x['callers'],only_standard_axioms=True));post();save()
  for q in r['fresh_modules']:req(sha(q['path'])==q['sha256'],'Changed earlier fresh object.')
  r.update(status='PASS',named_axiom_probes=sum(len(x['names'])for x in stage),callers=sum(x['callers']for x in stage),only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
