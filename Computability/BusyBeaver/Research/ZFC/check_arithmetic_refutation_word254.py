"""Fresh guarded check of the all-internal explicit refutation word.

Reuses exactly the 38 source/object prerequisites from successful Correct5/13.
No dependency build, download, or broad BusyBeaver umbrella check occurs.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time,tempfile

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,m):
 if not b:raise RuntimeError(m)
MODULE='BusyBeaver.ZFC.ArithmeticRefutationWord254'
SOURCE=Path('Computability/BusyBeaver/Lean')/Path(MODULE.replace('.','/')).with_suffix('.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_refutation_word254_audit.lean')
SOURCE_HASH='18cb3922d0479ea0b65cbaa1ac806c05be69aa0664e55624ff843847468e8fde'
AUDIT_HASH='a278e57f8390dc923318bfdd6b5f3d25ef91e4a68be149b1184dd3a8590cc828'
PROBES=['SetTheory.'+MODULE+'.'+n for n in ('resetCircuit_eval','refutationWord_defined','refutationWord_total','refutationWord_ne_zero','eval_terminator_falsity','proof_then_terminator','eval_refutationWord_state','stateValue_projections','eval_refutationWord','represented_refutation','refutation_exists')]
EXTERNAL={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
def project_source(repo,mod):
 if mod=='FirstOrder.Fol':return repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
 require(mod.startswith('BusyBeaver.ZFC.'),'Unexpected project module '+mod)
 return repo/'Computability/BusyBeaver/Lean'/Path(mod.replace('.','/')).with_suffix('.lean')
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ('repo','dependency-root','correct-evidence'):p.add_argument('--'+key,type=Path,required=True)
 for key in ('source','audit','output','correct-cache','lean'):p.add_argument('--'+key,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 require(__debug__,'Assertions must remain enabled; do not use -O.')
 repo=a.repo.resolve();depRoot=a.dependency_root.resolve();ep=a.correct_evidence.resolve();e=json.loads(ep.read_text())
 require(e['status']=='PASS'and e['named_axiom_probes']==5 and e['callers']==13 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Need actual Correct5/13PASS.')
 rows=[dict(q)for q in e['reused_modules']]
 fresh=e.get('fresh_modules')
 if fresh is not None:
  require(len(fresh)==1 and fresh[0]['module']=='BusyBeaver.ZFC.ArithmeticProofWordCorrect254','Expected one fresh Correct object.')
  fq=fresh[0]
 else:fq=dict(e['module_object'],module='BusyBeaver.ZFC.ArithmeticProofWordCorrect254')
 require(fq.get('source_sha256',e['source']['sha256'])==e['source']['sha256'],'Correct fresh source hash differs from source record.')
 rows.append(dict(module=fq['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],object=fq['path'],object_sha256=fq['sha256']))
 require(len(rows)==38 and len({q['module']for q in rows})==38,'Need38 prerequisites.')
 for q in rows:
  q['source']=str(project_source(repo,q['module']))
  if a.correct_cache:q['object']=str(a.correct_cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
  require(digest(q['source'])==q['source_sha256']and digest(q['object'])==q['object_sha256'],'Changed source/object '+q['module'])
 helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('correct_cantor_helper',helper);h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
 libs,deps=h.dependency_libraries(depRoot,a.library_path)
 for name in ('Foundation','Mathlib'):require(deps[name]['pin']==e['dependencies'][name]['pin']and deps[name]['tracked_clean']and e['dependencies'][name]['tracked_clean'],'Pin/clean mismatch.')
 require(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Manifest mismatch.')
 require(set(deps['providers'])==set(e['dependencies']['providers']),'Base providers differ.')
 for name,q in deps['providers'].items():require(q['sha256']==e['dependencies']['providers'][name]['sha256'],'Base provider hash differs.')
 providers=[];prior=e['providers']
 require(len(prior)==4 and {q['module']for q in prior}==EXTERNAL,'Need exact4 external providers.')
 for q in prior:
  rel=Path(q['module'].replace('.','/'));actual=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  source=Path(deps['Foundation'if q['module'].startswith('Foundation.')else'Mathlib']['path'])/rel.with_suffix('.lean')
  require(actual is not None and digest(actual)==q['object_sha256']and digest(source)==q['source_sha256'],'Wrong first external provider/source.')
  providers.append(dict(q,source=str(source),object=str(actual.resolve())))
 lean,version=h.compiler_path(a.lean or Path(e['compiler']['path']));require(digest(lean)==e['compiler']['sha256']and version==e['compiler']['version'],'Compiler mismatch.')
 src=a.source.resolve()if a.source else repo/SOURCE;audit=a.audit.resolve()if a.audit else repo/AUDIT;module=MODULE
 require(a.source is not None or digest(src)==SOURCE_HASH,'Maintained source changed; pass reviewed override.')
 require(a.audit is not None or digest(audit)==AUDIT_HASH,'Maintained audit changed; pass reviewed override.')
 require(h.lean_imports(src.read_text())==['BusyBeaver.ZFC.ArithmeticProofWordCorrect254'],'Unexpected imports.')
 require(h.lean_imports(audit.read_text())==[module],'Unexpected audit imports.')
 available={q['module']:q for q in rows};seen=set();external=set()
 def visit(m):
  if m.startswith(('Foundation.','Mathlib.')):external.add(m);return
  if m in seen:return
  require(m in available,'Missing project '+m);seen.add(m)
  for imp in h.lean_imports(Path(available[m]['source']).read_text()):visit(imp)
 visit('BusyBeaver.ZFC.ArithmeticProofWordCorrect254');require(seen==set(available),'Not exact project closure.')
 require(external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'},'Unexpected direct external imports.')
 externalProviders=[]
 for m in sorted(external):
  rel=Path(m.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dr=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);source=dr/rel.with_suffix('.lean');require(obj and source.is_file(),'Missing direct external provider.')
  externalProviders.append(dict(module=m,source=str(source),source_sha256=digest(source),object=str(obj.resolve()),object_sha256=digest(obj),actual_first_provider=True))
 expected=re.findall(r'^#print axioms (\S+)$',audit.read_text(),re.M);callers=len(re.findall(r'^example\b',audit.read_text(),re.M))
 require(expected==PROBES and callers==12,'Audit must retain exact ordered11 probes/12 callers.')
 require(all(n.startswith('SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.')for n in expected),'Unexpected axiom probe.')
 work=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-refutation-word-'));require(not work.is_relative_to(repo)and not work.is_relative_to(depRoot)and(not work.exists()or not any(work.iterdir())),'Fresh external output required.');work.mkdir(parents=True,exist_ok=True);cache=work/'cache';cache.mkdir();snap=work/'sources';local=snap/'BusyBeaver/ZFC';local.mkdir(parents=True);ss=local/src.name;aa=snap/'Audit.lean';shutil.copyfile(src,ss);shutil.copyfile(audit,aa)
 firstProjects=[]
 for q in rows:
  dst=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(Path(q['object']).resolve())
  require(digest(dst)==q['object_sha256'],'Wrong project overlay.')
  firstProjects.append(dict(module=q['module'],path=str(dst),resolved=str(dst.resolve()),sha256=digest(dst),actual_first_provider=True))
 inputs=[Path(__file__).resolve(),helper,ep,src,audit,ss,aa,lean,depRoot/'lake-manifest.json']+[Path(q[k])for q in rows+providers+externalProviders for k in ('source','object')];inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):digest(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-internal accepted falsity proof supplies a represented halting word from every working code. No scheduler, arithmetic-to-binary transport, or PA consistency endpoint.',correct_evidence=dict(path=str(ep),sha256=digest(ep)),source=dict(path=str(src),sha256=digest(src),snapshot=str(ss)),audit=dict(path=str(audit),sha256=digest(audit),snapshot=str(aa)),compiler=dict(e['compiler'],path=str(lean),version=version),reused_modules=rows,reused_count=38,source_override=a.source is not None,audit_override=a.audit is not None,providers=providers,direct_external_providers=externalProviders,actual_project_providers=firstProjects,exact_project_import_closure=True,dependencies=deps,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,memory_limit_mib=4096)
 def save():(work/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 save()
 def postchecks():
  after={q:digest(q)for q in before};require(after==before,'Changed input/provider/compiler.')
  for q in rows+providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next((x/rel for x in [cache,*libs]if(x/rel).is_file()),None)
   require(actual is not None and actual.resolve()==Path(q['object']).resolve()and digest(actual)==q['object_sha256'],'Changed first provider.')
  _,ad=h.dependency_libraries(depRoot,a.library_path);require(ad==deps,'Dependency state changed.')
  d.update(after=after,all_input_provider_postchecks=True)
 if a.prepare_only:postchecks();save();print(work/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(lean),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();r=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;(work/(label+'.log')).write_text(out);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=out));save();require(r.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 try:
  obj=cache/Path(module.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=digest(obj);d['fresh_modules']=[dict(module=module,path=str(obj),sha256=oh,source_sha256=digest(src))];save();out=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);require([n for n,_ in reports]==expected,'Wrong axiom reports.');require(all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Unexpected axiom.')
  postchecks();require(digest(obj)==oh,'Fresh object changed.')
  d.update(status='PASS',all_input_provider_postchecks=True,all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=11,callers=12,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[x.strip()for x in ax.split(',')if x.strip()])for n,ax in reports],warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except BaseException:d['status']='FAIL';save();raise
 save();print(work/'verification.json')
if __name__=='__main__':main()
