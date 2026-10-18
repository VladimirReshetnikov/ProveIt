#!/usr/bin/env python3
"""Check the structural false-first catalogue-rank witness and two literal clients.
Reuse only the exact 33-project import closure from the recorded FiniteControlTable
PASS, with Init/Omega and no external project boundary. The older parent did not
record a pre-audit fresh-object capture; that historical limitation is retained.
Its 32 selected source/object pairs are traced to the original 169-unit ancestor,
without rebuilding or claiming to revalidate the other 137 ancestor modules.
The new source and five-probe/five-client audit share120s,-j1,-M4096 and default
proof limits. Prepare-only performs no compiler, version query or dependency build.
This is a rank-lookup prototype, with no execution-performance or AX endpoint claim.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.ArithmeticControlSourceRank254'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254.'
SOURCE_SHA='79adbe730e163928f516d388002fd6a1e1b7f84785f2d362d4889df63c3f3ae1'
AUDIT_SHA='a600e8b75a99f2b6347fbe12a23080e11fd9c725a69714da345720d8e478ca35'
PARENT_SHA='bc0de17e9ba4d66101775fde6c59eaeeac6878ce14e97bea885b62f438f1c1be'
PARENT_MODULE='BusyBeaver.ZFC.FiniteControlTable254'
PARENT_SOURCE_SHA='326c3d191c17c7c5d75ebafb85cc38a1361e5091cd5d7bdbb01c88b7e9649c2a'
PARENT_AUDIT_SHA='d89330f86692f8967c83535a71e9cf8ea3714c0bf7415de2e42471b41ee55ce6'
PARENT_OBJECT_SHA='4422e7635cf801f8da6d5c3be256f93d2944549bc3b915ec7db83d8e53ded21f'
ANCESTOR_SHA='e02e4cbac881f97bc59b6d5681209e358af702e7a9b8f95cb9bbc7c061b0d5e7'
COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
PROBES=['AtRank.bound','AtRank.lookup','source_of_atRank','source_354','source_6423']
EXPECTED_MODULES=['BusyBeaver.Core', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.BootPerm252', 'BusyBeaver.ZFC.FiniteControlTable254', 'BusyBeaver.ZFC.FiniteZipper', 'BusyBeaver.ZFC.Permutation252Frame', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RegisterBoxes253', 'BusyBeaver.ZFC.RegisterBoxesPerm252', 'BusyBeaver.ZFC.RegisterDecrementPerm252', 'BusyBeaver.ZFC.RegisterIncrementPerm252', 'BusyBeaver.ZFC.RegisterMarkPerm252', 'BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RegisterPathClean', 'BusyBeaver.ZFC.SiteCoverage', 'BusyBeaver.ZFC.SitePerm252', 'BusyBeaver.ZFC.SitesPerm252', 'BusyBeaver.ZFC.SitesPerm252Checks0', 'BusyBeaver.ZFC.SitesPerm252Checks1', 'BusyBeaver.ZFC.SitesPerm252Checks2', 'BusyBeaver.ZFC.SitesPerm252Checks3', 'BusyBeaver.ZFC.SitesPerm252Checks4', 'BusyBeaver.ZFC.SitesPerm252Checks5', 'BusyBeaver.ZFC.SitesPerm252Checks6', 'BusyBeaver.ZFC.SitesPerm252Checks7', 'BusyBeaver.ZFC.SymbolicPerm252', 'BusyBeaver.ZFC.Table253', 'BusyBeaver.ZFC.TablePerm252', 'BusyBeaver.ZFC.WritingRuns', 'BusyBeaver.ZFC.ZipperRuns']
TOOL_PINS={'Init':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','Lean.Elab.Tactic.Omega':'eb766bae1ab40110a853c7cca853e36e1f4aece010a09fa4dd9b1b48116953fe'}
p=argparse.ArgumentParser(description=__doc__)
for name in ('repo','table-evidence','output'):p.add_argument('--'+name,type=Path,required=True)
for name in ('source','audit'):p.add_argument('--'+name,type=Path)
p.add_argument('--prepare-only',action='store_true');args=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
R=args.repo.resolve();W=args.output.resolve();E=args.table_evidence.resolve()
assert not W.is_relative_to(R) and (not W.exists() or not any(W.iterdir()))
S=args.source.resolve() if args.source else R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticControlSourceRank254.lean'
A=args.audit.resolve() if args.audit else Path(__file__).resolve().parent / 'arithmetic_control_source_rank254_audit.lean'
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA and sha(E)==PARENT_SHA
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';assert sha(helper)==HELPER_SHA
spec=importlib.util.spec_from_file_location('source_rank_helpers',helper);H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
imports=lambda q:H.lean_imports(Path(q).read_text())
assert imports(S)==[PARENT_MODULE] and imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==5
for q in (S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text())
e=json.loads(E.read_text())
assert e['status']=='PASS' and e['prepare_only'] is False and e['named_axiom_probes']==14 and e['callers']==17
assert e['only_standard_axioms'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit']
assert e['before']==e['after'] and e['providers']==[] and e['exact_project_import_closure']
assert [q['label'] for q in e['commands']]==['source','audit'] and all(q['exit_code']==0 and not q.get('timed_out',False) for q in e['commands'])
# Exact legacy schema: never manufacture a historical pre-audit capture.
assert 'source_object_recorded_before_audit' not in e and 'source_pass_object' not in e and 'fresh_first_provider_before_audit' not in e
assert e['source']['sha256']==PARENT_SOURCE_SHA and e['audit']['sha256']==PARENT_AUDIT_SHA
assert len(e['fresh_modules'])==1;fresh=e['fresh_modules'][0]
assert fresh['module']==PARENT_MODULE and fresh['sha256']==PARENT_OBJECT_SHA and fresh['source_sha256']==PARENT_SOURCE_SHA
C=Path(e['compiler']['path']).resolve();assert sha(C)==e['compiler']['sha256']==COMPILER_SHA
toolroot=C.parent.parent/'lib/lean'
def recorded_first(module):
 rel=Path(module.replace('.','/')).with_suffix('.olean')
 return next(root/rel for root in [*[Path(x) for x in e['LEAN_PATH'].split(os.pathsep)],toolroot] if (root/rel).is_file())
parent_fresh=recorded_first(PARENT_MODULE)
assert parent_fresh.resolve()==Path(fresh['path']).resolve() and sha(parent_fresh)==PARENT_OBJECT_SHA
parent_inputs=[Path(q) for q in e['before']]
for q in parent_inputs:assert sha(q)==e['before'][str(q)]
for role in ('source','audit'):
 q=e[role];assert sha(q['path'])==sha(q['snapshot'])==q['sha256']==e['before'][str(Path(q['path']).resolve())]
 parent_inputs.extend([Path(q['path']),Path(q['snapshot'])])
ancestor=R/'Computability/BusyBeaver/Research/ZFC/results/command-word254-integration-verification.json'
assert e['provider_evidence']==[dict(path=str(ancestor),sha256=ANCESTOR_SHA)] and sha(ancestor)==ANCESTOR_SHA
anc=json.loads(ancestor.read_text())
assert anc['status']=='PASS169-unit source-verified integration' and anc['only_standard_axioms']
assert anc['all_source_identities_unchanged_after_check'] and anc['all_object_identities_unchanged_after_check'] and anc['all_reused_object_identities_unchanged_after_check']
assert anc['fresh_checks'] and all(q['exit_code']==0 for q in anc['fresh_checks']) and anc['audit']['exit_code']==0
assert anc['compiler']['sha256']==COMPILER_SHA
ancestor_pool={q['module']:q for q in anc['source_closure']};assert len(ancestor_pool)==169
actuals={q['module']:q for q in e['actual_first_providers']};assert len(actuals)==len(e['actual_first_providers'])==32
pool={};ancestor_selected=[]
def maintained_source(module):return R/'Computability/BusyBeaver/Lean'/Path(module.replace('.','/')).with_suffix('.lean')
for q in e['reused_modules']:
 m=q['module'];assert m not in pool
 assert all(e['before'][str(Path(q[k]).resolve())]==e['after'][str(Path(q[k]).resolve())]==q[k+'_sha256'] for k in ('source','object'))
 found=recorded_first(m);old=actuals[m]
 assert found.resolve()==Path(q['object']).resolve()==Path(old['actual_first']).resolve() and sha(found)==q['object_sha256']==old['sha256']
 aq=ancestor_pool[m]
 assert aq['sha256']==aq['post_source_sha256']==q['source_sha256'] and aq['olean_sha256']==aq['post_olean_sha256']==q['object_sha256']
 source=maintained_source(m);assert sha(source)==q['source_sha256']
 pool[m]=dict(module=m,source=str(source),source_sha256=q['source_sha256'],object=str(Path(q['object']).resolve()),object_sha256=q['object_sha256'])
 ancestor_selected.append(dict(module=m,source_sha256=aq['sha256'],object_sha256=aq['olean_sha256'],historical_object=aq['olean'],historical_evidence=aq.get('evidence'),current_selected_object=pool[m]['object']))
assert len(pool)==32 and set(pool)==set(actuals)
source=maintained_source(PARENT_MODULE);assert sha(source)==PARENT_SOURCE_SHA
pool[PARENT_MODULE]=dict(module=PARENT_MODULE,source=str(source),source_sha256=PARENT_SOURCE_SHA,object=str(parent_fresh.resolve()),object_sha256=PARENT_OBJECT_SHA)
tool_pool={q['module']:q for q in e['toolchain_providers']};assert set(tool_pool)==set(TOOL_PINS)
for m,q in tool_pool.items():
 ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean')
 assert sha(ref)==q['object_sha256']==q['toolchain_reference_sha256']==TOOL_PINS[m]
 assert recorded_first(m).resolve()==ref.resolve() and Path(q['actual_first']).resolve()==ref.resolve()
closure=[];visiting=set();direct_tools={'Init'}
def visit(m):
 if m in closure:return
 assert m in pool and m not in visiting,m
 visiting.add(m);q=pool[m]
 assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256'],m
 for n in imports(q['source']):
  if n in pool:visit(n)
  else:assert n in TOOL_PINS,n;direct_tools.add(n)
 visiting.remove(m);closure.append(m)
visit(PARENT_MODULE)
assert set(closure)==set(EXPECTED_MODULES)==set(pool) and len(closure)==33 and direct_tools==set(TOOL_PINS)
W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snap=W/'sources'
ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for m in closure:
 dest=cache/Path(m.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(pool[m]['object'])
def first(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 return next(root/rel for root in [cache,toolroot] if (root/rel).is_file())
actual=[]
for m in closure:
 q=pool[m];obj=first(m);assert obj.resolve()==Path(q['object']).resolve() and sha(obj)==q['object_sha256']
 actual.append(dict(module=m,actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
tool=[]
for m,h in sorted(TOOL_PINS.items()):
 ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');obj=first(m)
 assert obj.resolve()==ref.resolve() and sha(obj)==h
 tool.append(dict(module=m,object=str(ref),object_sha256=h,actual_first=str(obj),toolchain_reference=str(ref),toolchain_reference_sha256=h,actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,E,ancestor,C,S,A,ss,aa,*parent_inputs]
for q in pool.values():inputs.extend([Path(q['source']),Path(q['object'])])
inputs.extend(Path(q['object']) for q in tool);inputs=list(dict.fromkeys(q.resolve() for q in inputs));before={str(q):sha(q) for q in inputs}
env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1')
legacy=dict(source_capture_before_audit_recorded=False,fresh_first_provider_before_audit_recorded=False,first_provider_resolved_now_from_recorded_LEAN_PATH=str(parent_fresh),first_provider_sha256=PARENT_OBJECT_SHA)
r=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',scope=__doc__,prepare_only=args.prepare_only,compiler=dict(path=str(C),sha256=COMPILER_SHA,version=e['compiler']['version'],compiler_version_query_performed=False),source_overridden=args.source is not None,audit_overridden=args.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)],parent_summaries=[dict(label='finite_control_table',path=str(E),sha256=PARENT_SHA,fresh_module=PARENT_MODULE,legacy_first_provider_binding=legacy)],ancestor_provenance=dict(path=str(ancestor),sha256=ANCESTOR_SHA,selected_provider_bindings=ancestor_selected,other_ancestor_modules_rechecked=False,other_ancestor_modules=sorted(set(ancestor_pool)-set(pool))),reused_modules=[pool[m] for m in closure],project_module_count=33,exact_project_import_closure=True,providers=[],actual_direct_external_imports=[],toolchain_providers=tool,actual_direct_tool_imports=sorted(direct_tools),actual_first_providers=actual,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,coverage_guard_replay=False,bootstrap_replay=False,shared_wall_seconds=120,source_object_recorded_before_audit=False,limits=dict(threads=1,memory_mebibytes=4096,proof_limits='Lean defaults'))
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(q):sha(q) for q in inputs};assert before==after
 for m,q in pool.items():assert first(m).resolve()==Path(q['object']).resolve() and sha(first(m))==q['object_sha256']
 for q in tool:assert first(q['module']).resolve()==Path(q['object']).resolve() and sha(first(q['module']))==q['object_sha256']
 r.update(after=after,all_input_provider_postchecks=True)
save()
if args.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
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
 oh=sha(obj);fresh=dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S));r.update(source_object_recorded_before_audit=True,source_pass_object=dict(fresh,source_command_index=0),fresh_modules=[fresh]);assert first(MODULE).resolve()==obj.resolve();r['fresh_first_provider_before_audit']=dict(module=MODULE,path=str(first(MODULE)),sha256=oh);save()
 out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
 assert [n for n,_ in reports]==[PREFIX+n for n in PROBES]
 assert all({x.strip() for x in ax.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for _,ax in reports)
 post();assert sha(obj)==oh==sha(first(MODULE));r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=5,callers=5,only_standard_axioms=True,actual_axiom_sets=[dict(theorem=n,axioms=[x.strip() for x in ax.split(',') if x.strip()]) for n,ax in reports],warnings={q['label']:q['output'].count('warning:') for q in r['commands']})
except Exception as ex:
 r.update(status='FAIL',error=str(ex))
 try:post()
 except Exception as err:r['postcheck_error']=str(err)
 save();raise
save();print(W/'verification.json')
