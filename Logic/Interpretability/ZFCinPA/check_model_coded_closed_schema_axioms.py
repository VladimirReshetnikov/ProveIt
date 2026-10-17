"""Narrow unrestricted closed-schema check; reuses successful BindFree/schema objects, no dependency builds."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedClosedSchemaAxioms';PREFIX='LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.'
NAMES=['closeFormulaCode_defined','closeFormulaCode_isFormula','closeFormulaCode_schemaRecognizer','closedSeparation_recognized','closedReplacement_recognized','closedSeparation_mem_zf','closedReplacement_mem_zf','closedSeparation_mem_zfc','closedReplacement_mem_zfc','closedSeparation_zf_isProof','closedReplacement_zf_isProof','closedSeparation_zfc_isProof','closedReplacement_zfc_isProof']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(p,m):
 if not p:raise RuntimeError(m)
SOURCE_SHA256='1318983c7727a9a280fe872003b6eac45b0959aec11c9d99a262bf99721be3b6'
AUDIT_SHA256='3d3eb8ec5da7a092284aabfd824e0ef5f73b36fef4d24b3c17de09ec732b71c7'
def default_repo():
 for q in Path(__file__).resolve().parents:
  if(q/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return q
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo());p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 p.add_argument('--schema-evidence',type=Path);p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path);p.add_argument('--output',type=Path,required=True)
 p.add_argument('--bind-evidence',type=Path);p.add_argument('--bind-cache',type=Path);p.add_argument('--bind-source',type=Path)
 p.add_argument('--schema-cache',type=Path);p.add_argument('--lean',type=Path);p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args();require(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';E=(a.schema_evidence or P/'results/model-coded-schema-axioms-verification.json').resolve();S=(a.source or P/'Lean/ZFCinPA/ModelCodedClosedSchemaAxioms.lean').resolve();A=(a.audit or P/'Lean/ZFCinPA/ModelCodedClosedSchemaAxiomsAudit.lean').resolve();W=a.output.resolve()
 require(sha(S)==SOURCE_SHA256 and sha(A)==AUDIT_SHA256,'Wrong frozen source/audit.')
 require(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 Hfile=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('schema_helpers',Hfile);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H);C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);e=json.loads(E.read_text());B=(a.bind_evidence or P/'results/model-coded-bind-free-verification.json').resolve();b=json.loads(B.read_text())
 require(b['status']=='PASS'and b['named_axiom_probes']==15 and b['callers']==15 and b['only_standard_axioms']and b['all_input_provider_postchecks']and b['all_fresh_objects_unchanged_after_audit'],'Wrong BindFree evidence.')
 require(b['source']['sha256']=='f3a11fa8165406cec42a793a2cbd05c950b60cce867d374e5414ce867e3c36ce','Wrong BindFree checkpoint.')
 require(e['status']=='PASS'and e['named_axiom_probes']==11 and e['callers']==10 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong schema evidence.')
 require(e['source']['sha256']=='a9fb204ca4f00fd30d28edfcc409ad561337a8378eab0b574b21bf8607f1c760'and e['audit']['sha256']=='225b8c8ac25d145c57bbdfdbf9abb010e33a566cbbad085e0154f41cf07fb903','Wrong schema checkpoint.')
 require(sha(C)==e['compiler']['sha256']==b['compiler']['sha256']and version==e['compiler']['version']==b['compiler']['version'],'Changed compiler.')
 require(b['audit']['sha256']=='0e780400452ee4d7d5c3c2d5ea8987d114efb8ebfcd85f1a58f0a82099769ba7','Wrong BindFree audit.')
 for k in ['Foundation','Mathlib']:require(deps[k]['pin']==e['dependencies'][k]['pin']and deps[k]['tracked_clean']and e['dependencies'][k]['tracked_clean'],'Changed dependency pin/state.')
 require(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']==b['dependencies']['lake_manifest_sha256'],'Changed dependency manifest.')
 require(b['dependencies']==e['dependencies'],'BindFree/schema dependency evidence differs.')
 for m,q in deps['providers'].items():require(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Changed base provider.')
 prior={q['module']:q for q in e['project_sources']};objects={q['module']:q for q in e['fresh_modules']};boundary={q['module']:q for q in e['providers']};project={};external={};visiting=set()
 bm='ZFCinPA.ModelCodedBindFree';bo=b['fresh_modules'][0];prior[bm]=dict(source_sha256=b['source']['sha256']);objects[bm]=bo
 schema_cache=a.schema_cache.resolve()if a.schema_cache else Path(objects['ZFCinPA.Instances']['path']).parents[1]
 require((schema_cache/'Foundation').is_dir(),'Missing full recorded Foundation namespace overlay.')
 def visit(m):
  if m in project or m in external:return
  require(m not in visiting,'Import cycle.');visiting.add(m)
  if m in prior:
   q=prior[m];o=objects[m];ss=(a.bind_source or P/'Lean/ZFCinPA/ModelCodedBindFree.lean').resolve()if m==bm else R/'Logic/Interpretability/ZFCinPA/Lean'/Path(m.replace('.','/')).with_suffix('.lean')if m.startswith('ZFCinPA.')else Path(deps['Foundation']['path'])/Path(m.replace('.','/')).with_suffix('.lean');obj=(a.bind_cache/Path(bm.replace('.','/')).with_suffix('.olean')).resolve()if m==bm and a.bind_cache else Path(bo['path'])if m==bm else schema_cache/Path(m.replace('.','/')).with_suffix('.olean');require(sha(ss)==q['source_sha256']==o['source_sha256']and sha(obj)==o['sha256'],'Changed recorded source/object: '+m)
   row=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(obj.resolve()),object_sha256=sha(obj),scope='Reused source-matched fresh object from schema PASS.')
   if m.startswith('ZFCinPA.'):project[m]=row
   else:external[m]=row
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   require(m in boundary,'Unrecorded external import '+m);q=boundary[m];rel=Path(m.replace('.','/'));dp=deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'];ss=Path(dp)/rel.with_suffix('.lean');obj=next((d/rel.with_suffix('.olean')for d in [schema_cache,*libs]if(d/rel.with_suffix('.olean')).is_file()),None);require(obj and sha(ss)==q['source_sha256']and sha(obj)==q['object_sha256'],'Changed boundary '+m);external[m]=dict(q,source=str(ss),object=str(obj.resolve()),scope='Recorded cached boundary; no whole-cache attestation.')
  visiting.remove(m)
 require(H.lean_imports(S.read_text())==['ZFCinPA.ModelCodedBindFree','ZFCinPA.ModelCodedSchemaAxioms'],'Wrong new imports.');require(H.lean_imports(A.read_text())==[MODULE],'Wrong audit imports.')
 for m in H.lean_imports(S.read_text()):visit(m)
 for m in deps['providers']:visit(m)
 require(set(project)=={'ZFCinPA.Instances','ZFCinPA.SchemaClosure','ZFCinPA.SeparationDelta1','ZFCinPA.ReplacementDelta1','ZFCinPA.ZFDelta1','ZFCinPA.ModelCodedSchemaAxioms',bm},'Wrong exact project closure.')
 selected={**project,**external};bind_selected={}
 for old in b['reused_modules']+b['providers']:
  m=old['module']
  if m in selected:
   now=selected[m];require(old['source_sha256']==now['source_sha256']and old['object_sha256']==now['object_sha256'],'BindFree/Closed selected provider disagreement: '+m);bind_selected[m]=dict(source_sha256=now['source_sha256'],object_sha256=now['object_sha256'])
 require(set(q['module']for q in b['reused_modules'])<=set(bind_selected),'Missing BindFree project predecessor provider.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);require(names==[PREFIX+n for n in NAMES]and len(re.findall(r'^example\b',A.read_text(),re.M))==13,'Wrong audit contract.')
 W.mkdir(parents=True);cache=W/'cache';(cache/'ZFCinPA').mkdir(parents=True);(cache/'Foundation').symlink_to((schema_cache/'Foundation').resolve(),target_is_directory=True)
 for q in project.values():
  obj=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.symlink_to(q['object'])
 snaps=W/'sources';ss=snaps/'ZFCinPA/ModelCodedClosedSchemaAxioms.lean';ss.parent.mkdir(parents=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 toolroot=C.parent.parent/'lib/lean';tool=[]
 direct_tool_imports={m for f in [S,A]+[Path(q['source'])for q in list(project.values())+list(external.values())]for m in H.lean_imports(f.read_text())if m.startswith('Lean.')}
 for m in sorted(direct_tool_imports|{'Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;obj=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None);require(obj and reference.is_file()and sha(obj)==sha(reference),'Different first-selected toolchain provider: '+m)
  for old in e.get('toolchain_providers',[]):
   if old['module']==m:require(sha(obj)==old['object_sha256'],'Changed recorded toolchain provider: '+m)
  for old in b.get('toolchain_providers',[]):
   if old['module']==m:require(sha(obj)==old['object_sha256'],'BindFree/Closed toolchain provider disagreement: '+m)
  tool.append(dict(module=m,object=str(obj.resolve()),object_sha256=sha(obj),actual_first=str(obj),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference),scope='Actual direct Lean imports plus Omega; first provider equals current pinned compiler sysroot object.'))
 inputs=[Path(__file__).resolve(),Hfile,E,B,C,S,A,ss,aa,D/'lake-manifest.json']+[Path(q[k])for q in list(project.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']];inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-internal arbitrary-free-label Sep/Rep closed axiom codes and direct proof codes; no repeated specialization or consistency endpoint.',source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),compiler=dict(path=str(C),sha256=sha(C),version=version),provider_evidence=[dict(path=str(E),sha256=sha(E)),dict(path=str(B),sha256=sha(B))],reused_modules=list(project.values()),providers=list(external.values()),bind_predecessor_provider_continuity=bind_selected,toolchain_providers=tool,actual_direct_tool_imports=sorted(direct_tool_imports),exact_project_import_closure=True,dependencies=deps,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(source=str(schema_cache/'Foundation'),target=str(cache/'Foundation'),scope='Read-only complete prior namespace tree; two prior fresh Foundation objects explicitly reused and hashed.'),dependency_build=False,downloads=False,historical_input_paths_scope='Original predecessor paths are historical; relocated selected source/object inputs are rehashed instead. Inherited unused paths are not asserted rechecked.')
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};require(before==after,'Changed inputs.');r['after']=after
  for q in list(project.values())+list(external.values()):
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next(d/rel for d in [cache,*libs]if(d/rel).is_file());require(actual.resolve()==Path(q['object']).resolve()and sha(actual)==q['object_sha256'],'Changed first provider.')
  for q in tool:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next(d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file());require(actual.resolve()==Path(q['object']).resolve()and sha(actual)==q['object_sha256']==sha(q['toolchain_reference']),'Changed first toolchain provider.')
  _,dd=H.dependency_libraries(D,a.library_path);require(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 def run(label,f,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(f)];t=time.monotonic();cp=subprocess.run(cmd,cwd=snaps,env=env,capture_output=True,text=True);out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,output=out));save();require(cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/'ZFCinPA/ModelCodedClosedSchemaAxioms.olean';run('source',ss,obj);oh=sha(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);require([n for n,_ in reports]==names and all(set(a.strip()for a in ax.split(',')if a.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();require(sha(obj)==oh,'Changed new object.');r.update(status='PASS',fresh_modules=[dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S))],all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=13,callers=13,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
