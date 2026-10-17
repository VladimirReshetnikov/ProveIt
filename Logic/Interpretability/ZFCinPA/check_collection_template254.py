"""Ordinary fixed Collection from three explicit schema resources; two fresh project modules, no dependency builds."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.CollectionTemplate254'
FRESH=[{'module': 'ZFCinPA.CollectionResources254', 'sha256': 'f7913a9fc5722044baf48c03b0d99376b7541a2cacbc605cd406e285a31661a4'}, {'module': 'ZFCinPA.CollectionTemplate254', 'sha256': '14b3321d729d9e690f72ef03aa4e379a7b8c347e7d999d7b92b8fb25c5d87d5f'}]
SPECS=[{'key': 'native', 'sha256': '74bca8ad3e63c7bbf6f36eb501a13ece8ff99f5ffe716dbb045c1adfbc4cf3af', 'module': 'ZFCinPA.NativeZFContainers254', 'probes': 15, 'callers': 15, 'source_sha256': '0e44d1d054f58cfa8afba6851d82878f47e70ad0e6d05a80715d6467d875154b', 'audit_sha256': '3e9d505e816157438df3e5218619401681f70ff96fd612cec93b3811e1e67d9f', 'fresh_modules': [{'module': 'ZFCinPA.NativeZFContainers254', 'source_sha256': '0e44d1d054f58cfa8afba6851d82878f47e70ad0e6d05a80715d6467d875154b', 'object_sha256': 'b7c33013f1a397c442c63cdccd5c9325ef357870e1a39041fce2e945031a5ed3'}]}, {'key': 'open', 'sha256': '6239b2396972db2ed461a7180a4774cf5733883ecee298fccafdb24cb1d39095', 'module': 'ZFCinPA.OpenSetTemplateCompiler', 'probes': 8, 'callers': 8, 'source_sha256': 'e58918ba722aa0a5cb7263ec6352f9141f2098da9d43a139bb2c3d79d4dcaedb', 'audit_sha256': '4bdea7c46ed5bd5967937f573a6a37242a4f9bc4ae4b45fdaf0a609e9f8247d2', 'fresh_modules': [{'module': 'BoundedPAConsistency.TypedTemplateProofCompiler', 'source_sha256': '7fc9ff52262b3d50405af5821933e27510081fab5877992e2143dc2fc34bf105', 'object_sha256': '74206b76d84a73eb89516e71dd65f6324a3db1022231de8fcda5a0d0a4e700b1'}, {'module': 'ZFCinPA.SetPlaceholders', 'source_sha256': 'afe63f2d6f6cd600e67a6f194457930b91ce413f771dc65a7eb0433d272f25b1', 'object_sha256': '08084ab5d4a907661b0455fdadce9340cf19e7e0e4571e1d90fff12f74649fe5'}, {'module': 'ZFCinPA.OpenSetTemplateCompiler', 'source_sha256': 'e58918ba722aa0a5cb7263ec6352f9141f2098da9d43a139bb2c3d79d4dcaedb', 'object_sha256': 'b47952cb5263e3924114bf3c2076d33abf0ed5ed07d8f59fbdba68f0c0a21cfd'}]}]
PROJECTS=['BoundedPAConsistency.TypedTemplateProofCompiler', 'BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.OmegaRecursion', 'BusyBeaver.ZFC.InternalOrd', 'BusyBeaver.ZFC.InternalRank', 'BusyBeaver.ZFC.NamedZF', 'BusyBeaver.ZFC.ZFRank', 'FirstOrder.Calculus', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf', 'ZFCinPA.Instances', 'ZFCinPA.NativeZFContainers254', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.SetPlaceholders', 'ZFCinPA.ZFDelta1']
EXTERNALS=['Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Mathlib.Tactic.Ring']
ROOTS={'ZFCinPA': 'Logic/Interpretability/ZFCinPA/Lean', 'BusyBeaver': 'Computability/BusyBeaver/Lean', 'FirstOrder': 'Logic/FirstOrder/Lean', 'BoundedZFCConsistency': 'SetTheory/BoundedConsistency/Lean', 'ZF': 'SetTheory/ZF/Lean', 'BoundedPAConsistency': 'Logic/PeanoArithmetic/BoundedConsistency/Lean'}
NAMES=['LeanProofs.ZFCinPA.CollectionResources254.leastRank_exists', 'LeanProofs.ZFCinPA.CollectionResources254.totalRank_total', 'LeanProofs.ZFCinPA.CollectionResources254.totalRank_ordinal', 'LeanProofs.ZFCinPA.CollectionResources254.collection', 'LeanProofs.ZFCinPA.CollectionTemplate254.eval_toFormula', 'LeanProofs.ZFCinPA.CollectionTemplate254.models_collection', 'LeanProofs.ZFCinPA.CollectionTemplate254.collection_provable']
AUDIT_SHA='7002167dcdb680e67a034c1a44de62ac846b254ffde733159ef62b22df27287c'
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
 for key in ['resources-source','source','audit']+[s['key']+'-'+v for s in SPECS for v in ['evidence','source','audit']]:p.add_argument('--'+key,type=Path)
 p.add_argument('--project-cache',type=Path);p.add_argument('--namespace-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 req(__debug__,'Do not use Python -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();P=R/'Logic/Interpretability/ZFCinPA';W=a.output.resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir())),'Fresh external output required.')
 sources={FRESH[0]['module']:(a.resources_source or P/'Lean'/Path(FRESH[0]['module'].replace('.','/')).with_suffix('.lean')).resolve(),MODULE:(a.source or P/'Lean'/Path(MODULE.replace('.','/')).with_suffix('.lean')).resolve()}
 A=(a.audit or P/'Lean/ZFCinPA/CollectionTemplate254Audit.lean').resolve()
 for q in FRESH:req(sha(sources[q['module']])==q['sha256'],'Wrong frozen fresh source '+q['module'])
 req(sha(A)==AUDIT_SHA,'Wrong frozen audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path)
 records=[];parent_evidence=[];parent_files=[];prior={};boundary={};overrides={}
 for spec in SPECS:
  key=spec['key'];path=(getattr(a,key+'_evidence')or P/'results'/('native-zf-containers254-verification.json'if key=='native'else'open-set-template-compiler-verification.json')).resolve()
  req(sha(path)==spec['sha256'],'Wrong exact parent evidence '+key);e=json.loads(path.read_text());records.append(e);parent_evidence.append(dict(key=key,path=str(path),sha256=sha(path)))
  req(e['status']=='PASS'and e['named_axiom_probes']==spec['probes']and e['callers']==spec['callers']and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong parent PASS contract '+key)
  req((e['source']['sha256'],e['audit']['sha256'])==(spec['source_sha256'],spec['audit_sha256']),'Wrong parent source/audit metadata '+key)
  fresh_meta=[dict(module=q['module'],source_sha256=q['source_sha256'],object_sha256=q['sha256'])for q in e['fresh_modules']];req(fresh_meta==spec['fresh_modules'],'Wrong exact parent fresh object list '+key)
  ss=(getattr(a,key+'_source')or P/'Lean'/Path(spec['module'].replace('.','/')).with_suffix('.lean')).resolve();aa=(getattr(a,key+'_audit')or P/'Lean/ZFCinPA'/(spec['module'].split('.')[-1]+'Audit.lean')).resolve()
  req(sha(ss)==spec['source_sha256']and sha(aa)==spec['audit_sha256'],'Changed parent source/audit '+key);parent_files.extend([ss,aa]);overrides[spec['module']]=ss
  req(sha(C)==e['compiler']['sha256']and version==e['compiler']['version'],'Different compiler '+key)
  for dep in ['Foundation','Mathlib']:req(e['dependencies'][dep]['pin']==deps[dep]['pin']and e['dependencies'][dep]['tracked_clean']and deps[dep]['tracked_clean'],'Different dependency pin/state '+key)
  req(e['dependencies']['lake_manifest_sha256']==deps['lake_manifest_sha256'],'Different manifest '+key)
  for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Different dependency discovery anchor '+key)
  for q in e['reused_modules']+[dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256'])for q in e['fresh_modules']]:
   m=q['module']
   if m in prior:req((q['source_sha256'],q['object_sha256'])==(prior[m]['source_sha256'],prior[m]['object_sha256']),'Inconsistent shared project '+m)
   else:prior[m]=q
  for q in e['providers']:
   m=q['module']
   if m in boundary:req((q['source_sha256'],q['object_sha256'])==(boundary[m]['source_sha256'],boundary[m]['object_sha256']),'Inconsistent shared external '+m)
   else:boundary[m]=q
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(records[1]['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete existing Foundation namespace.')
 selected={};external={};fresh_order=[];visiting=set();tools=set();actual_external=set()
 def visit(m,anchor=False):
  if m in selected or m in external or m in fresh_order:
   if m in external and not anchor:actual_external.add(m)
   return
  if m in {'Init','Std','Lean'}or m.startswith(('Init.','Std.','Lean.')):tools.add(m);return
  req(m not in visiting,'Import cycle '+m);visiting.add(m);rel=Path(m.replace('.','/'))
  if m in sources:
   for n in H.lean_imports(sources[m].read_text()):visit(n)
   fresh_order.append(m)
  elif m in prior:
   old=prior[m];req(m.split('.')[0]in ROOTS,'Unknown project root '+m);ss=(overrides.get(m)or R/ROOTS[m.split('.')[0]]/rel.with_suffix('.lean')).resolve();o=(a.project_cache/rel.with_suffix('.olean')if a.project_cache else Path(old['object'])).resolve()
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected project '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m];root=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=root/rel.with_suffix('.lean')
   o=next((d/rel.with_suffix('.olean')for d in [namespace.parent,*libs]if(d/rel.with_suffix('.olean')).is_file()),None)
   req(o and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed external boundary '+m)
   external[m]=dict(module=m,source=str(ss.resolve()),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope='Selected direct source/object boundary or explicit discovery anchor; transitive namespace cache not independently rebuilt.')
   if not anchor:actual_external.add(m)
  visiting.remove(m)
 expected_imports={FRESH[0]['module']:['BusyBeaver.ZFC.ZFRank'],MODULE:['ZFCinPA.SetPlaceholders','ZFCinPA.NativeZFContainers254',FRESH[0]['module']]}
 for m in sources:req(H.lean_imports(sources[m].read_text())==expected_imports[m],'Wrong fresh source imports '+m)
 req(H.lean_imports(A.read_text())==[MODULE],'Wrong audit imports.')
 for q in FRESH:visit(q['module'])
 for m in deps['providers']:visit(m,anchor=True)
 req(set(selected)==set(PROJECTS)and set(external)==set(EXTERNALS)and fresh_order==[q['module']for q in FRESH],'Wrong exact selected/fresh closure.')
 required_parent_fresh={'ZFCinPA.NativeZFContainers254','ZFCinPA.SetPlaceholders','BoundedPAConsistency.TypedTemplateProofCompiler'}
 req(required_parent_fresh<=set(selected),'An actual precursor fresh object was omitted.')
 req('ZFCinPA.OpenSetTemplateCompiler'not in selected and'ZFCinPA.BufferedTemplateProofCompiler'not in selected,'Unneeded parent client imported.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);req(names==NAMES and len(re.findall(r'^example\b',A.read_text(),re.M))==12,'Wrong focused audit contract.')
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';snapshots=[]
 for q in FRESH:
  f=sources[q['module']];ss=snaps/Path(q['module'].replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,ss);snapshots.append(dict(module=q['module'],path=str(f),sha256=sha(f),snapshot=str(ss)))
 aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
 files=[*sources.values(),A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]
 tools.update(m for f in files for m in H.lean_imports(f.read_text())if m in {'Init','Std','Lean'}or m.startswith(('Init.','Std.','Lean.')))
 toolroot=C.parent.parent/'lib/lean';tool=[]
 for m in sorted(tools|{'Init','Std','Lean','Lean.Elab.Tactic.Omega'}):
  rel=Path(m.replace('.','/')).with_suffix('.olean');reference=toolroot/rel;o=next((d/rel for d in [cache,*libs,toolroot]if(d/rel).is_file()),None)
  req(o and reference.is_file()and sha(o)==sha(reference),'Wrong actual first toolchain provider '+m)
  for old in [q for e in records for q in e.get('toolchain_providers',[])]:
   if old['module']==m:req(sha(o)==old['object_sha256'],'Different parent toolchain provider '+m)
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,C,A,aa,D/'lake-manifest.json',*parent_files]+[Path(q['path'])for q in parent_evidence]+[Path(q[k])for q in snapshots for k in ['path','snapshot']]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Ordinary Collection from exactly three predicate-dependent schema sentences, pure lifted ZF and explicit extended equality. Two fresh source modules; no internal G or PA comparison.',compiler=dict(path=str(C),sha256=sha(C),version=version),sources=snapshots,audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),parent_evidence=parent_evidence,reused_modules=list(selected.values()),providers=list(external.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(tools),actual_external_imports=sorted(actual_external),checked_discovery_only_anchors=sorted(set(external)-actual_external),dependencies=deps,exact_project_import_closure=True,required_parent_fresh_imported=sorted(required_parent_fresh),unused_parent_modules=sorted(set(prior)-set(selected)),unused_parent_boundaries=sorted(set(boundary)-set(external)),parent_scope='Native fixed ZF source plus its ten native ancestors; OpenSet record supplies ONLY its two freshly checked unchanged precursors and their actual closure. OpenSet/Buffered clients unimported; no Cantor or SetCongruence import.',before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),dependency_build=False,downloads=False)
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
  fresh=[]
  for q in snapshots:
   o=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);run(q['module'],Path(q['snapshot']),o);fresh.append(dict(module=q['module'],path=str(o),sha256=sha(o),source_sha256=q['sha256']))
  out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
  req([n for n,_ in reports]==names and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong axiom reports.');post();req(all(sha(q['path'])==q['sha256']for q in fresh),'Changed fresh object.')
  r.update(status='PASS',fresh_modules=fresh,named_axiom_probes=7,callers=12,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
