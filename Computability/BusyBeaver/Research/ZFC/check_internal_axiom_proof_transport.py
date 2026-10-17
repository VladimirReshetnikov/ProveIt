"""Check the same-language all-internal axiom-proof transport, using existing caches.
Only this new module/audit are built. No dependency download/build or whole-cache
attestation. Run in assertion-enabled Python with an empty external output dir.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='BoundedPAConsistency.InternalAxiomProofTransport'
PROBES=['LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport.'+n for n in ('derivable_of_axioms_provable','provable_of_axioms_provable','provable_iff_of_mutual_axiom_provability')]
BASIC='Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic'
SOURCE=Path('Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalAxiomProofTransport.lean')
AUDIT=Path('Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalAxiomProofTransportAudit.lean')
SOURCE_HASH='8efca1f6d357ee37b6cb0a08d684b48bf41ceae775b67182942de1b26ec473ad'
AUDIT_HASH='326e0bd28075df6ec2d3273355e691b48cff6a67fad9ceac6298dde01146fd7f'
def require(p,m):
 if not p:raise RuntimeError(m)
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ('repo','dependency-root','output'):p.add_argument('--'+k,type=Path,required=True)
 for k in ('source','audit'):p.add_argument('--'+k,type=Path)
 p.add_argument('--lean',type=Path,default=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'))
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 require(__debug__,'Do not use Python -O.')
 repo=a.repo.resolve();dep=a.dependency_root.resolve();src=a.source.resolve()if a.source else repo/SOURCE;audit=a.audit.resolve()if a.audit else repo/AUDIT;out=a.output.resolve()
 require(a.source is not None or digest(src)==SOURCE_HASH,'Changed maintained source; pass reviewed override.')
 require(a.audit is not None or digest(audit)==AUDIT_HASH,'Changed maintained audit; pass reviewed override.')
 require(not out.is_relative_to(repo)and not out.is_relative_to(dep)and(not out.exists()or not any(out.iterdir())),'Output must be fresh and external.')
 helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('cantor_helper',helper);h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
 libs,deps=h.dependency_libraries(dep,a.library_path);lean,version=h.compiler_path(a.lean)
 require(h.lean_imports(src.read_text())==[BASIC],'Unexpected source imports.')
 require(h.lean_imports(audit.read_text())==[MODULE],'Unexpected audit imports.')
 require(re.findall(r'^#print axioms (\S+)$',audit.read_text(),re.M)==PROBES,'Wrong probes.')
 require(len(re.findall(r'^example\b',audit.read_text(),re.M))==7,'Wrong caller count.')
 names=[BASIC,*deps['providers']];providers=[]
 for m in names:
  rel=Path(m.replace('.','/'));obj=next((lib/rel.with_suffix('.olean')for lib in libs if(lib/rel.with_suffix('.olean')).is_file()),None)
  dr=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);s=dr/rel.with_suffix('.lean')
  require(obj and s.is_file(),'Missing prebuilt provider '+m)
  providers.append(dict(module=m,source=str(s),source_sha256=digest(s),object=str(obj.resolve()),object_sha256=digest(obj),actual_first_provider=True))
 out.mkdir(parents=True,exist_ok=True);snaps=out/'sources';snap=snaps/'BoundedPAConsistency';snap.mkdir(parents=True);ss=snap/src.name;aa=snaps/'Audit.lean';shutil.copyfile(src,ss);shutil.copyfile(audit,aa);cache=out/'cache';(cache/'BoundedPAConsistency').mkdir(parents=True)
 inputs=[Path(__file__).resolve(),helper,src,audit,ss,aa,lean,dep/'lake-manifest.json']+[Path(q[k])for q in providers for k in ('source','object')];inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):digest(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-internal same-language proof transport conditional on represented provability of well-formed source axioms; no interpretation or C254/ZFC comparison.',source=dict(path=str(src),sha256=digest(src),snapshot=str(ss)),audit=dict(path=str(audit),sha256=digest(audit),snapshot=str(aa)),compiler=dict(path=str(lean),version=version,sha256=digest(lean)),dependencies=deps,providers=providers,reused_project_modules=[],exact_project_prerequisite_count=0,source_override=a.source is not None,audit_override=a.audit is not None,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(out/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 def post():
  require({p:digest(p)for p in before}==before,'Changed input.');d['after']={p:digest(p)for p in before}
  for q in providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next((lib/rel for lib in [cache,*libs]if(lib/rel).is_file()),None)
   require(actual and actual.resolve()==Path(q['object']).resolve()and digest(actual)==q['object_sha256'],'Changed actual first provider.')
  _,newdeps=h.dependency_libraries(dep,a.library_path);require(newdeps==deps,'Changed dependency state.');d['all_input_provider_postchecks']=True
 save()
 if a.prepare_only:post();save();print(out/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(lean),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();r=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);text=r.stdout+r.stderr;(out/(label+'.log')).write_text(text);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=text));save();require(r.returncode==0 and'sorryAx'not in text and"declaration uses 'sorry'"not in text,text);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return text
 try:
  obj=cache/'BoundedPAConsistency/InternalAxiomProofTransport.olean';run('source',ss,obj);oh=digest(obj);d['fresh_modules']=[dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=digest(src))];output=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",output,re.S)
  require([n for n,_ in reports]==PROBES,'Wrong reports.');require(all(set(s.strip()for s in ax.split(',')if s.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Unexpected axiom.')
  post();require(digest(obj)==oh,'Fresh object changed.')
  d.update(status='PASS',named_axiom_probes=3,callers=7,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,axiom_reports=[dict(theorem=n,axioms=[s.strip()for s in ax.split(',')if s.strip()])for n,ax in reports],warnings=sum(c['output'].count('warning:')for c in d['commands']))
 except BaseException:d['status']='FAIL';save();raise
 save();print(out/'verification.json')
if __name__=='__main__':main()
