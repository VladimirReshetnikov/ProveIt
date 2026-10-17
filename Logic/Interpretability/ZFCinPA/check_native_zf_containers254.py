"""Narrow ordinary Foundation-ZF container theorem; reuse exact native169 rank closure. No dependency builds."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.NativeZFContainers254'
PREFIX='LeanProofs.ZFCinPA.NativeZFContainers254.'
NAMES=['eval_toSet','sep_clause','sat_totalGraphF','sat_carveF','repl_clause','pair_clause','union_clause','succ_exists','inf_clause','pow_clause','reg_clause','zfAxioms_of_models','power_containers','zf_container_sentence','zf_containerRow_sentence']
CORE_SHA='e02e4cbac881f97bc59b6d5681209e358af702e7a9b8f95cb9bbc7c061b0d5e7'
BASIS_SHA='b59fab7eb413ad13f5e5264a5bac1d4b27b0bd280fc9588b4333e6fb81c6e7f1'
SOURCE_SHA='0e44d1d054f58cfa8afba6851d82878f47e70ad0e6d05a80715d6467d875154b'
AUDIT_SHA='3e9d505e816157438df3e5218619401681f70ff96fd612cec93b3811e1e67d9f'
PROJECTS={'BoundedZFCConsistency.Basic','BoundedZFCConsistency.OmegaRecursion','BusyBeaver.ZFC.InternalOrd','BusyBeaver.ZFC.InternalRank','BusyBeaver.ZFC.NamedZF','BusyBeaver.ZFC.ZFRank','FirstOrder.Calculus','FirstOrder.Completeness','FirstOrder.Fol','ZF.Zf'}
BOUNDARY='Foundation.FirstOrder.SetTheory.Basic.Axioms'
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
 p.add_argument('--core-evidence',type=Path);p.add_argument('--core-cache',type=Path)
 p.add_argument('--basis-evidence',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 E=(a.core_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/command-word254-integration-verification.json').resolve();B=(a.basis_evidence or P/'results/model-coded-decoder-rho1-254-verification.json').resolve()
 S=(a.source or P/'Lean/ZFCinPA/NativeZFContainers254.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/NativeZFContainers254Audit.lean').resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit.')
 req(sha(E)==CORE_SHA and sha(B)==BASIS_SHA,'Wrong exact historical provider evidence.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 e=json.loads(E.read_text());b=json.loads(B.read_text())
 req(e['status'].startswith('PASS')and e['units']==169 and e['audit']['exit_code']==0 and e['only_standard_axioms']and e['all_source_identities_unchanged_after_check']and e['all_object_identities_unchanged_after_check']and e['all_reused_object_identities_unchanged_after_check']and all(q['exit_code']==0 for q in e['fresh_checks']),'Wrong native169 PASS contract.')
 req(b['status']=='PASS'and b['named_axiom_probes']==10 and b['callers']==16 and b['only_standard_axioms']and b['all_input_provider_postchecks']and b['all_fresh_objects_unchanged_after_audit'],'Wrong rho1 boundary evidence contract.')
 req(b['source']['sha256']=='8a962f910ae4795838e5607ee43b10ae1037b75667d76dcf1f3998a231ff8314'and b['audit']['sha256']=='6242ab516f6bc7ca20dd0deccd21cd138dec9b99f8042895a421fb9c1b0c62f7','Wrong rho1 boundary checkpoint.')
 for record in [e,b]:req(sha(C)==record['compiler']['sha256']and version==record['compiler']['version'],'Different compiler.')
 for dep in ['Foundation','Mathlib']:req(deps[dep]['pin']==b['dependencies'][dep]['pin']and deps[dep]['tracked_clean']and b['dependencies'][dep]['tracked_clean'],'Different dependency pin/state.')
 req(deps['lake_manifest_sha256']==b['dependencies']['lake_manifest_sha256'],'Different manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==b['dependencies']['providers'][m]['sha256'],'Different unused dependency-discovery anchor.')
 prior={}
 for q in e['source_closure']:
  path=Path(q['path']);req(not path.is_absolute()and '..'not in path.parts and path.suffix=='.lean'and '/Lean/'in path.as_posix(),'Unsafe core source path.')
  m=path.as_posix().split('/Lean/',1)[1].removesuffix('.lean').replace('/','.')
  req(m==q['module']and m not in prior,'Wrong or duplicate core module path.');prior[m]=q
 corecache=(a.core_cache or Path(e['cache'])).resolve();req(corecache.is_dir(),'Missing existing native cache.')
 selected={};visiting=set();tool_direct=set()
 def visit(m):
  if m in selected:return
  req(m not in visiting and m in prior,'Unrecorded/cyclic native dependency '+m);visiting.add(m)
  old=prior[m];ss=(R/old['path']).resolve();o=(corecache/Path(m.replace('.','/')).with_suffix('.olean')).resolve()
  req(m.split('.')[0]in {'BoundedZFCConsistency','BusyBeaver','FirstOrder','ZF'},'Wrong native project root.')
  req(sha(ss)==old['sha256']==old['post_source_sha256']and sha(o)==old['olean_sha256']==old['post_olean_sha256'],'Changed native predecessor '+m)
  selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o),object_sha256=sha(o),scope='Selected native169 source/object identity, not an unrelated full umbrella rebuild.')
  for n in H.lean_imports(ss.read_text()):
   if n in prior:visit(n)
   else:req(n in {'Init','Std','Lean'}or n.startswith(('Init.','Std.','Lean.')),'Unexpected native boundary '+n);tool_direct.add(n)
  visiting.remove(m)
 req(H.lean_imports(S.read_text())==['BusyBeaver.ZFC.ZFRank',BOUNDARY]and H.lean_imports(A.read_text())==[MODULE],'Wrong direct source/audit imports.')
 visit('BusyBeaver.ZFC.ZFRank');req(set(selected)==PROJECTS,'Wrong exact rank project closure.')
 boundary_rows=[q for q in b['providers']if q['module']==BOUNDARY];req(len(boundary_rows)==1,'Missing verified Basic.Axioms boundary.');old=boundary_rows[0]
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(b['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete existing Foundation namespace.')
 rel=Path(BOUNDARY.replace('.','/'));bs=Path(deps['Foundation']['path'])/rel.with_suffix('.lean')
 bo=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
 req(bo and sha(bs)==old['source_sha256']and sha(bo)==old['object_sha256'],'Changed selected Foundation Basic.Axioms boundary.')
 boundary=dict(module=BOUNDARY,source=str(bs.resolve()),source_sha256=sha(bs),object=str(bo.resolve()),object_sha256=sha(bo),scope='Only this recorded direct Foundation source/object boundary is attested; its whole transitive namespace cache is not independently rebuilt.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==15,'Wrong focused audit.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 sourcefiles=[S,A,bs]+[Path(q['source'])for q in selected.values()]
 for f in sourcefiles:
  tool_direct.update(m for m in H.lean_imports(f.read_text())if m in {'Init','Std','Lean'}or m.startswith(('Init.','Std.','Lean.')))
 toolroot=C.parent.parent/'lib/lean';tool=[]
 # Init is implicit. Std/Lean are explicit guard anchors, whether imported or not.
 for m in sorted(tool_direct|{'Init','Std','Lean','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for q in b.get('toolchain_providers',[]):
   if q['module']==m:req(sha(o)==q['object_sha256'],'Different recorded toolchain provider.')
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference),scope='Actual direct import'if m in tool_direct else'Implicit Init or explicit canonical Std/Lean/Omega guard anchor; unused imports are not claimed.'))
 inputs=[Path(__file__).resolve(),helper,E,B,C,D/'lake-manifest.json',S,A,ss,aa]+[Path(q[k])for q in list(selected.values())+[boundary]for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]+[Path(q['path'])for q in deps['providers'].values()]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Ordinary Foundation ZF semantic extraction and two fixed power-container sentences (canonical row order included); no arbitrary internal matrix, numeric C or PA endpoint.',compiler=dict(path=str(C),sha256=sha(C),version=version),source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),core_evidence=dict(path=str(E),sha256=sha(E),scope='Exact native169; only ten actual rank prerequisites selected.'),basis_evidence=dict(path=str(B),sha256=sha(B),scope='Exact rho1 PASS supplies only compiler/dependency identities and recorded direct Basic.Axioms boundary; no rho1 project object or Cantor imported.'),reused_modules=list(selected.values()),providers=[boundary],toolchain_providers=tool,actual_direct_tool_imports=sorted(tool_direct),dependencies=deps,unused_dependency_discovery_anchors=list(deps['providers']),exact_project_import_closure=True,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+[boundary]+tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file());req(o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider.')
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)];t=time.monotonic();c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save();req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  o=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run('source',ss,o);oh=sha(o);out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==names and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(sha(o)==oh,'Changed fresh object.')
  r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(o),sha256=oh,source_sha256=sha(S))],named_axiom_probes=15,callers=15,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
