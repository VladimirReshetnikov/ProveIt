#!/usr/bin/env python3
"""Guarded actual AX prefix controls41..66→67, with its dispatch composition.
Reuse exactly98 project providers from the pinned ParamPush PASS plus its six
cached Foundation/Mathlib boundaries and Init/Omega toolchain boundaries.
Only source and audit are compiled: shared120s, -j1 -M4096, default proof limits.
Prepare-only performs no compiler/version query. No dependency build or download.
This is a shared interpreter result; the inherited binary relation is Perm252.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.ArithmeticControlAXPrefix254'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.'
SOURCE_SHA='aa960f901038154b76755b90a724bfd19cc3140928a964e280104b8119e61388'
AUDIT_SHA='2545695571ef17ddafd1cd9a59d2d1abf998078b8f9903e55beed0750551100e'
PARENT_SHA='098ef8d4de3d1451c35c243de0b205e512b3bbde04c3b227e7b76117945b55e7'
PARENT_MODULE='BusyBeaver.ZFC.ArithmeticControlParamPush254'
PARENT_SOURCE='9134d13759d19f7ac84181a5abab2179c60e64703b4dc9edbcaa4fd98ebdc8a1'
PARENT_AUDIT='9e3777020817b27e0da625e6d1aa1c29a61983c68d74109adf577d6dd9b19a5d'
PARENT_OBJECT='c405deca7433efdf3f181cdc51bbdbaafa25cbe8b6598302f08e408a246f2574'
PROBES=['entry_source','nextPush_source','parameterCopy_source','ax_push_run','ax_parameter_copy_run','ax_prefix_run','dispatch_ax_prefix_run']
BOUNDARIES={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Arithmetic.Exponential.Exp','Foundation.FirstOrder.Arithmetic.Definability.Absoluteness'}
DIRECT_BOUNDARIES=BOUNDARIES-{'Foundation.FirstOrder.Arithmetic.HFS.Seq'}
TOOL_BOUNDARIES={'Init','Lean.Elab.Tactic.Omega'}
EXPECTED_MODULES=['BusyBeaver.Core', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.ArithmeticBootstrapPerm252', 'BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCode254', 'BusyBeaver.ZFC.ArithmeticControlClear254', 'BusyBeaver.ZFC.ArithmeticControlCompare254', 'BusyBeaver.ZFC.ArithmeticControlData254', 'BusyBeaver.ZFC.ArithmeticControlDispatch254', 'BusyBeaver.ZFC.ArithmeticControlFetch254', 'BusyBeaver.ZFC.ArithmeticControlFrame254', 'BusyBeaver.ZFC.ArithmeticControlNip254', 'BusyBeaver.ZFC.ArithmeticControlPair254', 'BusyBeaver.ZFC.ArithmeticControlParamPush254', 'BusyBeaver.ZFC.ArithmeticControlRead254', 'BusyBeaver.ZFC.ArithmeticControlReadTemplate254', 'BusyBeaver.ZFC.ArithmeticControlRun254', 'BusyBeaver.ZFC.ArithmeticControlSimulation254', 'BusyBeaver.ZFC.ArithmeticControlStep254', 'BusyBeaver.ZFC.ArithmeticControlUnpair254', 'BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252', 'BusyBeaver.ZFC.ArithmeticFiniteControl254', 'BusyBeaver.ZFC.ArithmeticHistory254', 'BusyBeaver.ZFC.ArithmeticMachineGraphPerm252', 'BusyBeaver.ZFC.ArithmeticMachinePerm252', 'BusyBeaver.ZFC.ArithmeticMachinePrefixPerm252', 'BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252', 'BusyBeaver.ZFC.ArithmeticMachineRunPerm252', 'BusyBeaver.ZFC.ArithmeticMachineScanPerm252', 'BusyBeaver.ZFC.ArithmeticMachineStepPerm252', 'BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252', 'BusyBeaver.ZFC.ArithmeticPositiveSimulation254', 'BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252', 'BusyBeaver.ZFC.ArithmeticRegisterFilePerm252', 'BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252', 'BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252', 'BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252', 'BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252', 'BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252', 'BusyBeaver.ZFC.ArithmeticRow254', 'BusyBeaver.ZFC.ArithmeticSiteBootPerm252', 'BusyBeaver.ZFC.ArithmeticSitePerm252', 'BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252', 'BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252', 'BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252', 'BusyBeaver.ZFC.ArithmeticTapePrefix254', 'BusyBeaver.ZFC.ArithmeticTemplates254', 'BusyBeaver.ZFC.ArithmeticWritingScansPerm252', 'BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254', 'BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252', 'BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252', 'BusyBeaver.ZFC.BootPerm252', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.Code254History', 'BusyBeaver.ZFC.Code254Proof', 'BusyBeaver.ZFC.FiniteControlTable254', 'BusyBeaver.ZFC.FiniteZipper', 'BusyBeaver.ZFC.InstructionPerm252', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.Permutation252Frame', 'BusyBeaver.ZFC.Permutation252Simulation', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RegisterBoxes253', 'BusyBeaver.ZFC.RegisterBoxesPerm252', 'BusyBeaver.ZFC.RegisterDecrementPerm252', 'BusyBeaver.ZFC.RegisterIncrementPerm252', 'BusyBeaver.ZFC.RegisterMarkPerm252', 'BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RegisterPathClean', 'BusyBeaver.ZFC.RuntimeInstancePerm252', 'BusyBeaver.ZFC.RuntimePerm252', 'BusyBeaver.ZFC.SiteCoverage', 'BusyBeaver.ZFC.SitePerm252', 'BusyBeaver.ZFC.SitesPerm252', 'BusyBeaver.ZFC.SitesPerm252Checks0', 'BusyBeaver.ZFC.SitesPerm252Checks1', 'BusyBeaver.ZFC.SitesPerm252Checks2', 'BusyBeaver.ZFC.SitesPerm252Checks3', 'BusyBeaver.ZFC.SitesPerm252Checks4', 'BusyBeaver.ZFC.SitesPerm252Checks5', 'BusyBeaver.ZFC.SitesPerm252Checks6', 'BusyBeaver.ZFC.SitesPerm252Checks7', 'BusyBeaver.ZFC.SymbolicPerm252', 'BusyBeaver.ZFC.Table253', 'BusyBeaver.ZFC.TablePerm252', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'BusyBeaver.ZFC.WritingRuns', 'BusyBeaver.ZFC.ZipperRuns', 'FirstOrder.Fol']
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'

p=argparse.ArgumentParser(description=__doc__)
for key in ('repo','dependency-root','param-push-evidence','output'):p.add_argument('--'+key,type=Path,required=True)
for key in ('source','audit'):p.add_argument('--'+key,type=Path)
p.add_argument('--library-path',type=Path,action='append',default=[])
p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();E=a.param_push_evidence.resolve()
assert not W.is_relative_to(R) and not W.is_relative_to(D) and (not W.exists() or not any(W.iterdir()))
S=a.source.resolve() if a.source else R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticControlAXPrefix254.lean'
A=a.audit.resolve() if a.audit else Path(__file__).resolve().parent / 'arithmetic_control_ax_prefix254_audit.lean'
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA and sha(E)==PARENT_SHA
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';assert sha(helper)==HELPER_SHA
spec=importlib.util.spec_from_file_location('ax_prefix_helpers',helper);H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
imports=lambda q:H.lean_imports(Path(q).read_text())
assert imports(S)==[PARENT_MODULE] and imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==8
for q in (S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text())
e=json.loads(E.read_text())
assert e['status']=='PASS' and e['named_axiom_probes']==12 and e['callers']==22
assert e['only_standard_axioms'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit']
assert e['before']==e['after'] and e['source_object_recorded_before_audit']
assert [q['label'] for q in e['commands']]==['source','audit'] and all(q['exit_code']==0 and not q['timed_out'] for q in e['commands'])
assert e['source']['sha256']==PARENT_SOURCE and e['audit']['sha256']==PARENT_AUDIT
assert len(e['fresh_modules'])==1;fresh=e['fresh_modules'][0]
assert fresh['module']==PARENT_MODULE and fresh['sha256']==PARENT_OBJECT and fresh['source_sha256']==PARENT_SOURCE
assert e['source_pass_object']['sha256']==PARENT_OBJECT and e['source_pass_object']['source_sha256']==PARENT_SOURCE and e['source_pass_object']['source_command_index']==0
C=Path(e['compiler']['path']).resolve();assert sha(C)==e['compiler']['sha256'];toolroot=C.parent.parent/'lib/lean'
compiler=dict(path=str(C),sha256=sha(C),version=e['compiler']['version'],compiler_version_query_performed=False)
libs,deps=H.dependency_libraries(D,a.library_path)
for n in ('Foundation','Mathlib'):
 assert deps[n]['pin']==e['dependencies'][n]['pin'] and deps[n]['tracked_clean'] and e['dependencies'][n]['tracked_clean']
assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
for m,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][m]['sha256']
def source(m):
 return R/('Logic/FirstOrder/Lean' if m=='FirstOrder.Fol' else 'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
pool={}
for q in e['reused_modules']+[dict(module=PARENT_MODULE,source_sha256=PARENT_SOURCE,object=fresh['path'],object_sha256=PARENT_OBJECT)]:
 m=q['module'];row=dict(module=m,source=str(source(m)),source_sha256=q['source_sha256'],object=str(Path(q['object']).resolve()),object_sha256=q['object_sha256'])
 if m in pool:assert pool[m]==row
 else:pool[m]=row
assert len(pool)==98
providers={q['module']:dict(q) for q in e['providers']};assert set(providers)==BOUNDARIES
for m,q in providers.items():
 dep='Foundation' if m.startswith('Foundation.') else 'Mathlib';rel=Path(m.replace('.','/'))
 q['source']=str(Path(deps[dep]['path'])/rel.with_suffix('.lean'))
 obj=next(root/rel.with_suffix('.olean') for root in libs if (root/rel.with_suffix('.olean')).is_file())
 assert sha(q['source'])==q['source_sha256'] and sha(obj)==q['object_sha256'];q['object']=str(obj.resolve());q['actual_first_provider']=True
closure=[];visiting=set();external=set();direct_tools={'Init'}
is_tool=lambda m:m=='Init' or m.startswith(('Init.','Lean.','Std.'))
def visit(m):
 if m in closure:return
 assert m in pool and m not in visiting,m
 visiting.add(m);q=pool[m]
 assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256'],m
 for n in imports(q['source']):
  if n in pool:visit(n)
  elif is_tool(n):direct_tools.add(n)
  else:assert n in BOUNDARIES,n;external.add(n)
 visiting.remove(m);closure.append(m)
for m in imports(S):visit(m)
assert set(closure)==set(EXPECTED_MODULES) and len(closure)==98 and external==DIRECT_BOUNDARIES
selected={m:pool[m] for m in closure}
# External dependencies remain explicit cached boundaries. Their own imports
# are not represented as newly revalidated transitive project modules.
for q in providers.values():
 for m in imports(q['source']):
  if is_tool(m):direct_tools.add(m)
tool_pool={q['module']:q for q in e['toolchain_providers']};assert set(tool_pool)==TOOL_BOUNDARIES
assert direct_tools<=TOOL_BOUNDARIES
assert sha(e['source']['snapshot'])==PARENT_SOURCE and sha(e['audit']['snapshot'])==PARENT_AUDIT
historical=[]
for q in e.get('inherited_unused_alternatives_not_rechecked',[]):
 assert q['selected'] is False
 historical.append(dict(q,current_check_selected=False,current_check_rehashed=False,current_scope='Inherited provenance only; not imported or rehashed in this run.'))
W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snap=W/'sources'
ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for m,q in selected.items():
 dest=cache/Path(m.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
def first(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 return next(root/rel for root in [cache,*libs,toolroot] if (root/rel).is_file())
actual=[]
for m,q in {**selected,**providers}.items():
 obj=first(m);assert obj.resolve()==Path(q['object']).resolve() and sha(obj)==q['object_sha256']
 actual.append(dict(module=m,actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
tool=[]
for m in sorted(TOOL_BOUNDARIES):
 q=tool_pool[m];ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');obj=first(m)
 assert obj.resolve()==ref.resolve() and sha(ref)==q['object_sha256']==q['toolchain_reference_sha256']
 tool.append(dict(module=m,object=str(ref),object_sha256=sha(ref),actual_first=str(obj),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,D/'lake-manifest.json',Path(e['source']['snapshot']),Path(e['audit']['snapshot'])]
for q in [*selected.values(),*providers.values()]:inputs.extend([Path(q['source']),Path(q['object'])])
inputs.extend(Path(q['object']) for q in tool);inputs=list(dict.fromkeys(q.resolve() for q in inputs));before={str(q):sha(q) for q in inputs}
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',scope=__doc__,prepare_only=a.prepare_only,compiler=compiler,source_overridden=a.source is not None,audit_overridden=a.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)],reused_modules=[selected[m] for m in closure],candidate_provider_count=len(pool),excluded_candidate_modules=sorted(set(pool)-set(closure)),project_module_count=len(closure),exact_project_import_closure=True,providers=list(providers.values()),external_project_boundaries=sorted(BOUNDARIES),actual_direct_external_imports=sorted(external),inherited_additional_external_boundary='Foundation.FirstOrder.Arithmetic.HFS.Seq',toolchain_providers=tool,actual_direct_tool_imports=sorted(direct_tools),actual_first_providers=actual,inherited_unused_alternatives_not_rechecked=historical,dependencies=deps,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,shared_wall_seconds=120,source_object_recorded_before_audit=False,limits=dict(threads=1,memory_mebibytes=4096,proof_limits='Lean defaults'))
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(q):sha(q) for q in inputs};assert before==after
 for m,q in {**selected,**providers}.items():assert sha(first(m))==q['object_sha256']
 for q in tool:assert sha(first(q['module']))==q['object_sha256']
 _,current=H.dependency_libraries(D,a.library_path);assert current==deps
 r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
deadline=time.monotonic()+120
def run(label,file,obj=None):
 cmd=[str(C),'-j1','-M4096','--root='+str(snap)]+(['-o',str(obj)] if obj else [])+[str(file)];began=time.monotonic();remaining=deadline-began;assert remaining>0
 try:
  cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True,timeout=remaining);out,code,timed_out=cp.stdout+cp.stderr,cp.returncode,False
 except subprocess.TimeoutExpired as ex:
  dec=lambda v:v.decode(errors='replace') if isinstance(v,bytes) else v or '';out,code,timed_out=dec(ex.stdout)+dec(ex.stderr)+'\nTIMEOUT\n',-1,True
 (W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-began,exit_code=code,timed_out=timed_out,timeout_seconds=remaining,output=out));save()
 assert code==0 and 'sorryAx' not in out and "declaration uses 'sorry'" not in out,out
 return out
try:
 obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj);assert obj.is_file() and not obj.is_symlink()
 oh=sha(obj);fresh=dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S));r.update(source_object_recorded_before_audit=True,source_pass_object=fresh,fresh_modules=[fresh]);assert first(MODULE).resolve()==obj.resolve();r['fresh_first_provider_before_audit']=dict(module=MODULE,path=str(first(MODULE)),sha256=oh);save()
 out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
 assert [n for n,_ in reports]==[PREFIX+n for n in PROBES]
 assert all({x.strip() for x in ax.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for _,ax in reports)
 post();assert sha(obj)==oh==sha(first(MODULE));r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=7,callers=8,only_standard_axioms=True,actual_axiom_sets=[dict(theorem=n,axioms=[x.strip() for x in ax.split(',') if x.strip()]) for n,ax in reports],warnings={q['label']:q['output'].count('warning:') for q in r['commands']})
except Exception as ex:
 r.update(status='FAIL',error=str(ex))
 try:post()
 except Exception as err:r['postcheck_error']=str(err)
 save();raise
save();print(W/'verification.json')
