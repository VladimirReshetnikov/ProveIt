"""Fresh eight-unit model-coded set-schema check with two explicit external prerequisites.
All five local schema prerequisites are built from maintained sources. The checker also source-checks exactly two pinned Foundation SetTheory.Basic
modules into scratch.
Other identified external providers are reused, without whole-cache attestation. New schema axiom/proof constructors and audit
are checked serially with pinned Lean4.32 and assertions enabled.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='ZFCinPA.ModelCodedSchemaAxioms';BASE='LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.'
NAMES=['schemaRecognizer_of_closed_body','sep_core_subst_identity','rep_core_subst_identity','sep_body_shift_fixed','rep_body_shift_fixed','sepBody_mem_zf_of_shift_fixed','repBody_mem_zf_of_shift_fixed','zfSeparationProof_isProof','zfReplacementProof_isProof','zfcSeparationProof_isProof','zfcReplacementProof_isProof']
FOUNDATION_ORDER=['Foundation.FirstOrder.SetTheory.Basic.Misc','Foundation.FirstOrder.SetTheory.Basic.Axioms']
PROJECT_ORDER=['ZFCinPA.Instances','ZFCinPA.SchemaClosure','ZFCinPA.SeparationDelta1','ZFCinPA.ReplacementDelta1','ZFCinPA.ZFDelta1',MODULE]
def require(p,m):
 if not p:raise RuntimeError(m)
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
SOURCE_SHA256='a9fb204ca4f00fd30d28edfcc409ad561337a8378eab0b574b21bf8607f1c760'
AUDIT_SHA256='225b8c8ac25d145c57bbdfdbf9abb010e33a566cbbad085e0154f41cf07fb903'
def default_repo():
 for p in Path(__file__).resolve().parents:
  if (p/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py').is_file():return p
 return Path.cwd()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,default=default_repo())
 p.add_argument('--dependency-root',type=Path,default=Path.home()/'src/Proofs')
 p.add_argument('--source',type=Path,help='default: maintained ModelCodedSchemaAxioms.lean')
 p.add_argument('--audit',type=Path,help='default: maintained ModelCodedSchemaAxiomsAudit.lean')
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--lean',type=Path,default=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'))
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 require(__debug__,'Assertions must stay enabled; do not use -O.')
 repo=a.repo.resolve();dep=a.dependency_root.resolve();project=repo/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA';src=(a.source or project/'ModelCodedSchemaAxioms.lean').resolve();audit=(a.audit or project/'ModelCodedSchemaAxiomsAudit.lean').resolve();out=a.output.resolve()
 require(src.is_file()and digest(src)==SOURCE_SHA256,'Wrong frozen schema source.')
 require(audit.is_file()and digest(audit)==AUDIT_SHA256,'Wrong frozen schema audit.')
 require(not out.is_relative_to(repo)and not out.is_relative_to(dep)and(not out.exists()or not any(out.iterdir())),'Fresh external output required.')
 helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';sp=importlib.util.spec_from_file_location('cantor_helper',helper);h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h);libs,deps=h.dependency_libraries(dep,a.library_path);lean,version=h.compiler_path(a.lean)
 order=FOUNDATION_ORDER+PROJECT_ORDER
 sources={m:repo/'Logic/Interpretability/ZFCinPA/Lean'/Path(m.replace('.','/')).with_suffix('.lean')for m in PROJECT_ORDER[:-1]};sources[MODULE]=src
 for m in FOUNDATION_ORDER:sources[m]=Path(deps['Foundation']['path'])/Path(m.replace('.','/')).with_suffix('.lean')
 seen=set();external=set()
 def visit(m):
  if m not in sources and m.startswith(('Foundation.','Mathlib.')):external.add(m);return
  require(m in sources,'Unexpected project import '+m)
  if m in seen:return
  seen.add(m)
  for n in h.lean_imports(sources[m].read_text()):visit(n)
 visit(MODULE);require(seen==set(order),'Wrong exact localproject closure.')
 require(h.lean_imports(src.read_text())==['ZFCinPA.ZFDelta1','Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed'],'Unexpected newmodule imports.')
 require(h.lean_imports(audit.read_text())==[MODULE],'Unexpected audit imports.');require(re.findall(r'^#print axioms (\S+)$',audit.read_text(),re.M)==[BASE+n for n in NAMES],'Wrong probes.');require(len(re.findall(r'^example\b',audit.read_text(),re.M))==10,'Wrong callers.')
 providers=[]
 for m in sorted(external|set(deps['providers'])):
  rel=Path(m.replace('.','/'));obj=next((lib/rel.with_suffix('.olean')for lib in libs if(lib/rel.with_suffix('.olean')).is_file()),None);dp=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path']);ss=dp/rel.with_suffix('.lean');require(obj and ss.is_file(),'Missing existing provider '+m);providers.append(dict(module=m,source=str(ss),source_sha256=digest(ss),object=str(obj.resolve()),object_sha256=digest(obj),actual_first_provider=True))
 out.mkdir(parents=True,exist_ok=True);snaps=out/'sources';(snaps/'ZFCinPA').mkdir(parents=True);cache=out/'cache';(cache/'ZFCinPA').mkdir(parents=True)
 # Lean resolves a package namespace through one root. Mirror untouched cached
 # Foundation branches into scratch so its two fresh modules share the exact
 # existing namespace, without writing through links or claiming whole-cache trust.
 namespace_mirrors=[]
 base=next(lib/'Foundation' for lib in libs if (lib/'Foundation').is_dir())
 targets=[Path(m.replace('.','/')).relative_to('Foundation')for m in FOUNDATION_ORDER]
 def mirror(source,dest,rel=Path()):
  dest.mkdir(parents=True,exist_ok=True)
  for item in source.iterdir():
   r=rel/item.name;dd=dest/item.name
   if item.is_dir() and any(t.is_relative_to(r)for t in targets):mirror(item,dd,r)
   elif item.is_file() and any(r.parent==t.parent and item.name.startswith(t.name+'.')for t in targets):continue
   else:dd.symlink_to(item.resolve(),target_is_directory=item.is_dir())
 mirror(base,cache/'Foundation');namespace_mirrors.append(dict(namespace='Foundation',cached_tree=str(base),scratch_tree=str(cache/'Foundation'),scope='Untouched branches are links; only two fresh module paths are writable. Only named boundary-provider bytes are attested.'))
 rows=[]
 for m in order:
  ss=snaps/Path(m.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(sources[m],ss);rows.append(dict(module=m,source=str(sources[m]),source_sha256=digest(sources[m]),snapshot=str(ss)))
 aa=snaps/'Audit.lean';shutil.copyfile(audit,aa)
 inputs=[Path(__file__).resolve(),helper,lean,dep/'lake-manifest.json',audit,aa]+[Path(q[k])for q in rows for k in ('source','snapshot')]+[Path(q[k])for q in providers for k in ('source','object')];inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):digest(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Actual internal Separation/Replacement recognizer membership and proofcarriers for shift-fixed matrices; no arbitraryfreeparameter closure or C254/ZFC comparison.',source=dict(path=str(src),sha256=digest(src),snapshot=str(snaps/'ZFCinPA/ModelCodedSchemaAxioms.lean')),audit=dict(path=str(audit),sha256=digest(audit),snapshot=str(aa)),compiler=dict(path=str(lean),version=version,sha256=digest(lean)),project_sources=rows,exact_project_closure=PROJECT_ORDER,fresh_external_prerequisites=FOUNDATION_ORDER,fresh_external_scope='Only two pinned Foundation SetTheory.Basic files are compiled into scratch; source checkout untouched.',providers=providers,namespace_mirrors=namespace_mirrors,dependencies=deps,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=True,full_dependency_build=False,dependency_checkout_mutated=False,downloads=False)
 def save():(out/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 def post():
  require({x:digest(x)for x in before}==before,'Changed input/provider/compiler.');d['after']={x:digest(x)for x in before}
  for q in providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next((lib/rel for lib in[cache,*libs]if(lib/rel).is_file()),None);require(first and first.resolve()==Path(q['object']).resolve()and digest(first)==q['object_sha256'],'Changed first external provider.')
  for q in d['fresh_modules']:require(digest(q['path'])==q['sha256'],'Changed fresh module object.')
  _,dd=h.dependency_libraries(dep,a.library_path);require(dd==deps,'Changed dependency state.');d.update(all_input_provider_postchecks=True,all_fresh_objects_unchanged_after_audit=True)
 save()
 if a.prepare_only:post();save();print(out/'verification.json');return
 def run(label,file,obj=None):
  cmd=[str(lean),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();rr=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True);text=rr.stdout+rr.stderr;(out/(label+'.log')).write_text(text);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=rr.returncode,output=text));save();require(rr.returncode==0 and'sorryAx'not in text and"declaration uses 'sorry'"not in text,text);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return text
 try:
  for q in rows:
   obj=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);run(q['module'],Path(q['snapshot']),obj);d['fresh_modules'].append(dict(module=q['module'],path=str(obj),sha256=digest(obj),source_sha256=q['source_sha256']));save()
  text=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.S);require([n for n,_ in reports]==[BASE+n for n in NAMES],'Wrong reports.');require(all(set(a.strip()for a in ax.split(',')if a.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Unexpected axiom.');post();d.update(status='PASS',named_axiom_probes=11,callers=10,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[a.strip()for a in ax.split(',')if a.strip()])for n,ax in reports],warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except BaseException:d['status']='FAIL';save();raise
 save();print(out/'verification.json')
if __name__=='__main__':main()
