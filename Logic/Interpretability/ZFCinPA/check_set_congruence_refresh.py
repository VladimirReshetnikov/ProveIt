"""Fresh unchanged SetPlaceholderQuotient → SetCongruence check; no dependency build/fetch.
Prepare-only hashes the inherited compiler binary without invoking it or --version.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
OPENSET_SHA='6239b2396972db2ed461a7180a4774cf5733883ecee298fccafdb24cb1d39095'
SOURCE_HASHES={'ZFCinPA.SetCongruence': 'a72c669ecd09b1fdb3dfb7aafbb9fd137fd7f6eda96f76f021f5de8e5bf4eaaf', 'ZFCinPA.SetPlaceholderQuotient': '7e6fca529d7787f039194e670de439f5450749fb959cff0b22586170c611f50a'}
PROJECTS=['BoundedPAConsistency.TypedTemplateProofCompiler', 'ZFCinPA.Instances', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.SetPlaceholders', 'ZFCinPA.ZFDelta1']
NEW_BOUNDARIES={'Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory': {'source_sha256': 'fdd7cca1553d3e09c1ff71d16e864a238ea37d224d1a5010bd89daf0574fd1ba', 'object_sha256': '8006936f3e334722033a827e93ccfec835fdd59fbd29fc703cf6c161d41c0294'}, 'Foundation.FirstOrder.Completeness': {'source_sha256': '9f202d14fc4b4ead948e932aa55a8fab581489d1ca98233384b5aad3186ac875', 'object_sha256': '9ad4e429ff4c08395f7a0ed99053ad5f04ae76daa4ff94647a76a6e342cac7cc'}, 'Foundation.Meta.ClProver': {'source_sha256': '9f53c313d83781a0b9e7b573f03e3b2a264bcc5bce0ae050c19864d1b622c726', 'object_sha256': '81f7ee5db3f30effacc4418b98a01071a963c284dd2cc040ddaab14d5ad3104e'}}
DIRECT_EXTERNALS=['Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding', 'Foundation.FirstOrder.Completeness', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Foundation.Meta.ClProver']
AUDIT_SHA='f263c56ea995155d24909df9997fc451bff6e186776add617cfcc2b079409bca'
NAMES=['LeanProofs.ZFCinPA.SetPlaceholderQuotient.models_setPlaceholderCongruence_iff', 'LeanProofs.ZFCinPA.SetPlaceholderQuotient.models_fullEquality', 'LeanProofs.ZFCinPA.SetPlaceholderQuotient.complete_underSetPlaceholderCongruence', "LeanProofs.ZFCinPA.SetCongruence.setReplace'", 'LeanProofs.ZFCinPA.SetCongruence.setReplace', 'LeanProofs.ZFCinPA.SetCongruence.congruenceProof₀', 'LeanProofs.ZFCinPA.SetCongruence.congruenceProof₁', 'LeanProofs.ZFCinPA.SetCongruence.congruenceProof₂', 'LeanProofs.ZFCinPA.SetCongruence.congruenceProof₃', 'LeanProofs.ZFCinPA.SetCongruence.translate_setPlaceholderCongruenceSentence', 'LeanProofs.ZFCinPA.SetCongruence.translate_setPlaceholderCongruence', 'LeanProofs.ZFCinPA.SetCongruence.translatedCongruenceProof']

FRESH=['ZFCinPA.SetPlaceholderQuotient','ZFCinPA.SetCongruence']
ROOTS={'ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean','BoundedPAConsistency':'Logic/PeanoArithmetic/BoundedConsistency/Lean'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def default_repo():
 for p in Path(__file__).resolve().parents:
  if(p/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return p
 return Path.cwd()
def module_rel(m,suffix):return Path(m.replace('.','/')).with_suffix(suffix)
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo())
 p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 p.add_argument('--open-set-evidence',type=Path,required=True)
 for k in ['quotient-source','congruence-source','audit','project-cache','namespace-cache','lean']:
  p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true')
 a=p.parse_args()
 if not __debug__:p.error('Python -O is unsupported: guards must be active.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();P=R/'Logic/Interpretability/ZFCinPA'
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or(W.is_dir()and not any(W.iterdir()))),'Fresh external output required.')
 E=a.open_set_evidence.resolve();req(sha(E)==OPENSET_SHA,'Wrong exact OpenSet run2 evidence.');e=json.loads(E.read_text())
 req(e['status']=='PASS'and e['named_axiom_probes']==8 and e['callers']==8 and e['warnings']==2 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong OpenSet PASS contract.')
 req(len(e['fresh_modules'])==3 and [q['module']for q in e['fresh_modules']]==['BoundedPAConsistency.TypedTemplateProofCompiler','ZFCinPA.SetPlaceholders','ZFCinPA.OpenSetTemplateCompiler'],'Wrong OpenSet fresh chain.')
 S={FRESH[0]:(a.quotient_source or P/'Lean/ZFCinPA/SetPlaceholderQuotient.lean').resolve(),FRESH[1]:(a.congruence_source or P/'Lean/ZFCinPA/SetCongruence.lean').resolve()}
 A=(a.audit or P/'Lean/ZFCinPA/SetCongruenceRefreshAudit.lean').resolve()
 req(all(sha(S[m])==SOURCE_HASHES[m]for m in FRESH)and sha(A)==AUDIT_SHA,'Changed frozen unchanged sources/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 oldhelpers=[h for q,h in e['before'].items()if q.endswith('/Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py')]
 req(len(oldhelpers)==1 and sha(helper)==oldhelpers[0],'Changed dependency helper.')
 sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C=(a.lean or Path(e['compiler']['path'])).expanduser().resolve();req(C.is_file()and sha(C)==e['compiler']['sha256'],'Changed pinned compiler binary.')
 version=e['compiler']['version'];req(version.startswith('Lean (version 4.32.0,'),'Wrong recorded compiler version.')
 if not a.prepare_only:
  observed=subprocess.check_output([str(C),'--version'],text=True).strip();req(observed==version,'Wrong actual compiler version.')
 libs,deps=H.dependency_libraries(D,a.library_path)
 for name in ['Foundation','Mathlib']:
  req(deps[name]['pin']==e['dependencies'][name]['pin']and e['dependencies'][name]['tracked_clean'],'Different dependency pin/state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Different dependency manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Changed base discovery provider '+m)
 prior={q['module']:q for q in e['reused_modules']}
 source_rows={q['module']:q for q in e['fresh_precursor_sources']}
 source_rows['ZFCinPA.OpenSetTemplateCompiler']=e['source']
 for q in e['fresh_modules']:
  s=source_rows[q['module']];req(q['source_sha256']==s['sha256'],'Wrong parent fresh source binding.')
  req(q['module']not in prior,'Duplicate parent module.')
  prior[q['module']]=dict(module=q['module'],source_sha256=s['sha256'],object=q['path'],object_sha256=q['sha256'])
 boundary={q['module']:q for q in e['providers']}
 req(not(set(NEW_BOUNDARIES)&set(boundary)),'New boundary unexpectedly inherited.')
 for m,q in NEW_BOUNDARIES.items():boundary[m]=dict(module=m,**q,scope='New explicitly frozen cached source/object boundary; not freshly rebuilt or whole-cache attested.')
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(e['namespace_overlay']['target'])).resolve()
 req(namespace.is_dir(),'Missing complete Foundation namespace mirror.')
 selected={};external={};fresh_visit=[];visiting=set()
 def visit(m):
  if m in selected or m in external or m in fresh_visit:return
  req(m not in visiting,'Import cycle.');visiting.add(m)
  if m in S:
   for n in H.lean_imports(S[m].read_text()):visit(n)
   fresh_visit.append(m)
  elif m.split('.')[0]in ROOTS:
   req(m in prior,'Unrecorded project '+m);old=prior[m]
   ss=R/ROOTS[m.split('.')[0]]/module_rel(m,'.lean')
   o=(a.project_cache/module_rel(m,'.olean')if a.project_cache else Path(old['object'])).resolve()
   req(sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed selected project '+m)
   selected[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o),object_sha256=sha(o))
   for n in H.lean_imports(ss.read_text()):visit(n)
  else:
   req(m in boundary,'Unrecorded external boundary '+m);old=boundary[m]
   root=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=root/module_rel(m,'.lean')
   o=next((d/module_rel(m,'.olean')for d in [namespace.parent,*libs]if(d/module_rel(m,'.olean')).is_file()),None)
   req(o is not None and sha(ss)==old['source_sha256']and sha(o)==old['object_sha256'],'Changed actual external boundary '+m)
   external[m]=dict(module=m,source=str(ss),source_sha256=sha(ss),object=str(o.resolve()),object_sha256=sha(o),scope=old.get('scope','Recorded cached source/object boundary; no whole-cache attestation.'))
  visiting.remove(m)
 expected_imports={FRESH[0]:['ZFCinPA.SetPlaceholders','Foundation.FirstOrder.Completeness'],FRESH[1]:['ZFCinPA.SetPlaceholderQuotient','Foundation.Meta.ClProver','Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory']}
 req(all(H.lean_imports(S[m].read_text())==expected_imports[m]for m in FRESH)and H.lean_imports(A.read_text())==[FRESH[-1]],'Wrong unchanged source/audit imports.')
 visit(FRESH[-1]);direct_external=set(external)
 for m in deps['providers']:visit(m)
 req(set(selected)==set(PROJECTS)and direct_external==set(DIRECT_EXTERNALS)and set(external)==set(DIRECT_EXTERNALS)|set(deps['providers'])and fresh_visit==FRESH,'Wrong exact project/fresh/boundary closure.')
 names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)
 req(names==NAMES and len(re.findall(r'^example\b',A.read_text(),re.M))==14,'Wrong ordered focused audit.')
 W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/module_rel(q['module'],'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 snaps=W/'sources';fresh_sources=[]
 for m in FRESH:
  dest=snaps/module_rel(m,'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(S[m],dest)
  fresh_sources.append(dict(module=m,path=str(S[m]),sha256=sha(S[m]),snapshot=str(dest)))
 aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
 files=list(S.values())+[A]+[Path(q['source'])for q in list(selected.values())+list(external.values())]
 direct_tools={m for f in files for m in H.lean_imports(f.read_text())if m in ['Init','Lean','Std']or m.startswith(('Lean.','Std.'))}
 tool=[];sysroot=C.parent.parent/'lib/lean';search=[cache,*libs,sysroot]
 for m in sorted(direct_tools|{'Init','Lean.Elab.Tactic.Omega'}):
  rel=module_rel(m,'.olean');reference=sysroot/rel;o=next((d/rel for d in search if(d/rel).is_file()),None)
  req(o is not None and reference.is_file()and sha(o)==sha(reference),'Wrong actual toolchain provider '+m)
  for old in e.get('toolchain_providers',[]):
   if old['module']==m:req(sha(o)==old['object_sha256'],'Changed inherited toolchain provider '+m)
  tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(reference),toolchain_reference_sha256=sha(reference)))
 inputs=[Path(__file__).resolve(),helper,E,C,A,aa,D/'lake-manifest.json']+[Path(q[k])for q in fresh_sources for k in ['path','snapshot']]+[Path(q[k])for q in list(selected.values())+list(external.values())for k in ['source','object']]+[Path(q[k])for q in tool for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Fresh unchanged two-module equality quotient/congruence check. Quotient helper is templateZFC; binary congruence/replacement is generic Δ1 T+EQ and audited for ZF, arbitrary internal K and free parameters. No Collection schema callback or G endpoint.',compiler=dict(path=str(C),sha256=sha(C),version=version),compiler_version_query_performed=not a.prepare_only,sources=fresh_sources,audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),open_set_evidence=dict(path=str(E),sha256=sha(E)),reused_modules=list(selected.values()),providers=list(external.values()),direct_external_boundaries=sorted(direct_external),discovery_anchor_modules=sorted(deps['providers']),new_cached_boundary_modules=sorted(NEW_BOUNDARIES),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct_tools),dependencies=deps,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace)),exact_project_import_closure=True,local_source_options={'SetPlaceholderQuotient.complete_underSetPlaceholderCongruence.maxHeartbeats':800000},global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False,source_overrides=dict(quotient=a.quotient_source is not None,congruence=a.congruence_source is not None,audit=a.audit is not None))
 def save():(W/'verification.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};req(before==after,'Changed input.');r['after']=after
  for q in list(selected.values())+list(external.values())+tool:
   rel=module_rel(q['module'],'.olean');o=next((d/rel for d in search if(d/rel).is_file()),None)
   req(o is not None and o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 def run(label,file,o=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(o)]if o else[])+[str(file)];t=time.monotonic()
  c=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);out=c.stdout+c.stderr;(W/(label+'.log')).write_text(out)
  r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=c.returncode,output=out));save()
  req(c.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 try:
  if a.prepare_only:post();save();print(W/'verification.json');return
  for q in fresh_sources:
   o=cache/module_rel(q['module'],'.olean');o.parent.mkdir(parents=True,exist_ok=True);run(q['module'],Path(q['snapshot']),o)
   r['fresh_modules'].append(dict(module=q['module'],path=str(o),sha256=sha(o),source_sha256=q['sha256']));save()
  out=run('audit',aa)
  reports=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.M)
  req([n for n,_ in reports]==names and all(set(z.strip()for z in ax.split(',')if z.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong ordered axiom reports.')
  post();req(all(sha(q['path'])==q['sha256']for q in r['fresh_modules']),'Changed fresh object through audit.')
  r.update(status='PASS',named_axiom_probes=12,callers=14,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException:r['status']='FAIL';save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
