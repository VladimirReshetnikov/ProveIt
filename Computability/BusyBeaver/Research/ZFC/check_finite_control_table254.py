"""Guarded derived actual leaf catalogue and deterministic finite source resolver.
Only the new Std-only source/audit are checked; selected source/object providers
are reused from native169. No coverage, bootstrap or dependency rebuild.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
p=argparse.ArgumentParser(description=__doc__)
for k in ('repo','core-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
for k in ('source','audit','cache','lean'):p.add_argument('--'+k,type=Path)
p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
R=a.repo.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('core_check_helpers',helper);H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
C,version=H.compiler_path(a.lean);E=a.core_evidence.resolve();assert sha(E)=='e02e4cbac881f97bc59b6d5681209e358af702e7a9b8f95cb9bbc7c061b0d5e7'
e=json.loads(E.read_text());assert e['status']=='PASS169-unit source-verified integration'and e['only_standard_axioms']and e['all_source_identities_unchanged_after_check']and e['all_object_identities_unchanged_after_check']and e['all_reused_object_identities_unchanged_after_check']
assert e['fresh_checks']and all(q['exit_code']==0 for q in e['fresh_checks'])and e['audit']['exit_code']==0
assert sha(C)==e['compiler']['sha256']and version==e['compiler']['version']
S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FiniteControlTable254.lean'
A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/finite_control_table254_audit.lean'
assert a.source is not None or sha(S)=='326c3d191c17c7c5d75ebafb85cc38a1361e5091cd5d7bdbb01c88b7e9649c2a'
assert a.audit is not None or sha(A)=='d89330f86692f8967c83535a71e9cf8ea3714c0bf7415de2e42471b41ee55ce6'
module='BusyBeaver.ZFC.FiniteControlTable254';prefix='SetTheory.BusyBeaver.ZFC.FiniteControlTable254.'
imports=['BusyBeaver.ZFC.SitesPerm252','BusyBeaver.ZFC.RegisterPathClean'];assert H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[module]
pool={q['module']:q for q in e['source_closure']};mods={};visiting=set();is_tool=lambda m:m=='Init'or m.startswith(('Std.','Lean.'))
def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
def visit(m):
 if m in mods:return
 assert m in pool and m not in visiting;visiting.add(m);q=pool[m];assert q['sha256']==q['post_source_sha256']and q['olean_sha256']==q['post_olean_sha256']
 f=source(m);obj=(a.cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))if a.cache else Path(q['olean']).resolve();assert sha(f)==q['sha256']and sha(obj)==q['olean_sha256']
 for n in H.lean_imports(f.read_text()):
  if not is_tool(n):visit(n)
 visiting.remove(m);mods[m]=dict(module=m,source=str(f),source_sha256=sha(f),object=str(obj),object_sha256=sha(obj))
for m in imports:visit(m)
assert 'BusyBeaver.ZFC.ActualTree254'in mods and 'BusyBeaver.ZFC.Prog254'in mods and all(not m.startswith(('Foundation.','Mathlib.'))for m in mods)
names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);expected=['leafEntries_length','leafEntries_sound','leafEntries_complete','leafEntries_nodup','actualEntries_length','source_accepted','source_walk','source_follow','source_injective','resolve_source','resolve_source_self','resolve_number_valid','first_source','empty_control'];assert names==[prefix+n for n in expected]and len(re.findall(r'^example\b',A.read_text(),re.M))==17
cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(module.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for q in mods.values():
 dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
toolroot=C.parent.parent/'lib/lean';actual=[]
for q in mods.values():
 rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(p/rel for p in[cache,toolroot]if(p/rel).is_file());assert sha(obj)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
direct_tool_imports={n for f in[S,A]+[Path(q['source'])for q in mods.values()]for n in H.lean_imports(f.read_text())if is_tool(n)};tool=[]
for m in sorted(direct_tool_imports|{'Lean.Elab.Tactic.Omega'}):
 rel=Path(m.replace('.','/')).with_suffix('.olean');ref=toolroot/rel;obj=next(p/rel for p in[cache,toolroot]if(p/rel).is_file());assert sha(obj)==sha(ref);tool.append(dict(module=m,object=str(obj.resolve()),object_sha256=sha(obj),actual_first=str(obj),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa]
for q in mods.values():inputs.extend([Path(q['source']),Path(q['object'])])
inputs.extend(Path(q[k])for q in tool for k in('object','toolchain_reference'));inputs=list(dict.fromkeys(p.resolve()for p in inputs));before={str(p):sha(p)for p in inputs};env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,provider_evidence=[dict(path=str(E),sha256=sha(E))],compiler=dict(path=str(C),version=version,sha256=sha(C)),source_overridden=a.source is not None,audit_overridden=a.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),exact_project_import_closure=True,providers=[],toolchain_providers=tool,actual_first_providers=actual,actual_direct_tool_imports=sorted(direct_tool_imports),before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,coverage_guard_replay=False,bootstrap_replay=False)
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(p):sha(p)for p in inputs};assert before==after
 for q in list(mods.values())+tool:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');obj=next(p/rel for p in[cache,toolroot]if(p/rel).is_file());assert sha(obj)==q['object_sha256']
 r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
def run(label,file,obj=None):
 cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,output=out));save();assert cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
try:
 obj=cache/Path(module.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=sha(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports);post();assert sha(obj)==oh;r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=sha(S))],named_axiom_probes=14,callers=17,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
save();print(W/'verification.json')
