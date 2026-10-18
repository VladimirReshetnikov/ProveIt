#!/usr/bin/env python3
"""Bounded exact246 external ZF/ZFC endpoint against three pinned successful parents.
Requires the complete actual410735 blank bootstrap frame, whole-frame runtime and
all102 grouped coverage modules, selected through the exact230-module import closure.
Fresh source/audit only; -j1 -M4096, shared120s and default proof limits.
Prepare-only performs no compiler/version query or dependency build.
This is an external Lean metatheorem, not an object-language PA derivation.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.BinaryPrefix246'
PREFIX='SetTheory.BusyBeaver.ZFC.BinaryPrefix246.'
SOURCE_SHA='ab50569977d8c8fe2eb5784a35e9f90fdca0ac2a01f211ccf18924a7e6a42478'
AUDIT_SHA='8da80d7c0f4bb4064b0a84c19911740499a3fb6e4ad2d6dd4b5571688d282e91'
PARENTS={'runtime': ('1965fff0430079cec4e3bb067a22ca05ef2d526fe97fae1e7c74fab1e7fa506f', 'BusyBeaver.ZFC.RuntimeInstancePrefix246'), 'bootstrap': ('4ccfd6f710e91939d72aef608f818b4356883fd4e112792bea01225d987c7262', 'BusyBeaver.ZFC.BootstrapFrame246'), 'coverage': ('f0679a8fe30e750ac6c58f2aada7f8ea3be7803e49cac4ffe05c64bfdbd4e2f6', 'BusyBeaver.ZFC.SitesPrefix246')}
EXPECTED_MODULES=['BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.Choice', 'BoundedZFCConsistency.CodePredicate', 'BoundedZFCConsistency.Coding', 'BoundedZFCConsistency.FormulaClosedSet', 'BoundedZFCConsistency.InternalSat', 'BoundedZFCConsistency.InternalSatTotality', 'BoundedZFCConsistency.OmegaRecursion', 'BusyBeaver.Core', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.Bisim254', 'BusyBeaver.ZFC.BootPrefix246Chunk001', 'BusyBeaver.ZFC.BootPrefix246Chunk002', 'BusyBeaver.ZFC.BootPrefix246Chunk003', 'BusyBeaver.ZFC.BootPrefix246Chunk004', 'BusyBeaver.ZFC.BootPrefix246Chunk005', 'BusyBeaver.ZFC.BootPrefix246Chunk006', 'BusyBeaver.ZFC.BootPrefix246Chunk007', 'BusyBeaver.ZFC.BootPrefix246Chunk008', 'BusyBeaver.ZFC.BootPrefix246First', 'BusyBeaver.ZFC.BootPrefix246Probe16384', 'BusyBeaver.ZFC.Bootstrap', 'BusyBeaver.ZFC.BootstrapFrame246', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.Code254Containers', 'BusyBeaver.ZFC.Code254GIC', 'BusyBeaver.ZFC.Code254Models', 'BusyBeaver.ZFC.CodeOrder', 'BusyBeaver.ZFC.CompositionModel', 'BusyBeaver.ZFC.Constructible', 'BusyBeaver.ZFC.ConstructibleAbs', 'BusyBeaver.ZFC.ConstructibleChoice', 'BusyBeaver.ZFC.ConstructibleDef', 'BusyBeaver.ZFC.ConstructibleOrder', 'BusyBeaver.ZFC.ConstructibleReflect', 'BusyBeaver.ZFC.ConstructibleZF', 'BusyBeaver.ZFC.Dag254', 'BusyBeaver.ZFC.DecodeFresh254', 'BusyBeaver.ZFC.DeepPositiveClosure', 'BusyBeaver.ZFC.DefinableClosure', 'BusyBeaver.ZFC.DirtyProgram254', 'BusyBeaver.ZFC.DirtyRoot254', 'BusyBeaver.ZFC.Enum254', 'BusyBeaver.ZFC.EnumSafeStart254', 'BusyBeaver.ZFC.FastTablePrefix246', 'BusyBeaver.ZFC.FiniteSets', 'BusyBeaver.ZFC.FiniteZipper', 'BusyBeaver.ZFC.InductiveAttempts', 'BusyBeaver.ZFC.InstructionPrefix246', 'BusyBeaver.ZFC.InternalOrd', 'BusyBeaver.ZFC.InternalRank', 'BusyBeaver.ZFC.InternalWO', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.L2Axioms254', 'BusyBeaver.ZFC.L2AxiomsEval254', 'BusyBeaver.ZFC.L2Control254', 'BusyBeaver.ZFC.L2Lib254', 'BusyBeaver.ZFC.L2Macros254', 'BusyBeaver.ZFC.L2Root254', 'BusyBeaver.ZFC.LogicalSeed246', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.NamedForm254', 'BusyBeaver.ZFC.NamedZF', 'BusyBeaver.ZFC.NativeDecoded254', 'BusyBeaver.ZFC.NativeTheory254', 'BusyBeaver.ZFC.OrderRec', 'BusyBeaver.ZFC.PSCCalibration', 'BusyBeaver.ZFC.Permutation252Frame', 'BusyBeaver.ZFC.PositiveClosure', 'BusyBeaver.ZFC.PowerSyntax', 'BusyBeaver.ZFC.Prefix246Boxes', 'BusyBeaver.ZFC.Prefix246Pulse', 'BusyBeaver.ZFC.Prefix246Simulation', 'BusyBeaver.ZFC.ProfileAxioms', 'BusyBeaver.ZFC.ProfileCollection', 'BusyBeaver.ZFC.ProfileComposition', 'BusyBeaver.ZFC.ProfileCongruence', 'BusyBeaver.ZFC.ProfileModel', 'BusyBeaver.ZFC.ProfilePairs', 'BusyBeaver.ZFC.ProfileSyntax', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.QuotientBasic', 'BusyBeaver.ZFC.QuotientCPGIC', 'BusyBeaver.ZFC.QuotientModel', 'BusyBeaver.ZFC.QuotientPower', 'BusyBeaver.ZFC.QuotientReplacement', 'BusyBeaver.ZFC.QuotientSeparation', 'BusyBeaver.ZFC.QuotientZF0', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RMEquiv254', 'BusyBeaver.ZFC.RegisterBoxes253', 'BusyBeaver.ZFC.RegisterBoxesPerm252', 'BusyBeaver.ZFC.RegisterMarkPerm252', 'BusyBeaver.ZFC.RegisterMarkPrefix246', 'BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RegisterPathClean', 'BusyBeaver.ZFC.RuntimeInstancePrefix246', 'BusyBeaver.ZFC.RuntimePerm252', 'BusyBeaver.ZFC.SatSupport', 'BusyBeaver.ZFC.SingletonInfinity', 'BusyBeaver.ZFC.SiteCoverage', 'BusyBeaver.ZFC.SitePrefix246', 'BusyBeaver.ZFC.SitesPrefix246', 'BusyBeaver.ZFC.SitesPrefix246Batch001', 'BusyBeaver.ZFC.SitesPrefix246Batch002', 'BusyBeaver.ZFC.SitesPrefix246Batch003', 'BusyBeaver.ZFC.SitesPrefix246Batch004', 'BusyBeaver.ZFC.SitesPrefix246Batch005', 'BusyBeaver.ZFC.SitesPrefix246Batch006', 'BusyBeaver.ZFC.SitesPrefix246Batch007', 'BusyBeaver.ZFC.SitesPrefix246Batch008', 'BusyBeaver.ZFC.SitesPrefix246Batch009', 'BusyBeaver.ZFC.SitesPrefix246Batch010', 'BusyBeaver.ZFC.SitesPrefix246Batch011', 'BusyBeaver.ZFC.SitesPrefix246Batch012', 'BusyBeaver.ZFC.SitesPrefix246Batch015', 'BusyBeaver.ZFC.SitesPrefix246Batch016', 'BusyBeaver.ZFC.SitesPrefix246Batch017', 'BusyBeaver.ZFC.SitesPrefix246Batch018', 'BusyBeaver.ZFC.SitesPrefix246Batch019', 'BusyBeaver.ZFC.SitesPrefix246Batch020', 'BusyBeaver.ZFC.SitesPrefix246Batch021', 'BusyBeaver.ZFC.SitesPrefix246Batch022', 'BusyBeaver.ZFC.SitesPrefix246Batch023', 'BusyBeaver.ZFC.SitesPrefix246Batch024', 'BusyBeaver.ZFC.SitesPrefix246Batch025', 'BusyBeaver.ZFC.SitesPrefix246Batch026', 'BusyBeaver.ZFC.SitesPrefix246Batch027', 'BusyBeaver.ZFC.SitesPrefix246Batch028', 'BusyBeaver.ZFC.SitesPrefix246Batch029', 'BusyBeaver.ZFC.SitesPrefix246Batch030', 'BusyBeaver.ZFC.SitesPrefix246Batch031', 'BusyBeaver.ZFC.SitesPrefix246Batch032', 'BusyBeaver.ZFC.SitesPrefix246Batch033', 'BusyBeaver.ZFC.SitesPrefix246Batch034', 'BusyBeaver.ZFC.SitesPrefix246Batch035', 'BusyBeaver.ZFC.SitesPrefix246Batch036', 'BusyBeaver.ZFC.SitesPrefix246Batch037', 'BusyBeaver.ZFC.SitesPrefix246Batch038', 'BusyBeaver.ZFC.SitesPrefix246Batch039', 'BusyBeaver.ZFC.SitesPrefix246Batch040', 'BusyBeaver.ZFC.SitesPrefix246Batch041', 'BusyBeaver.ZFC.SitesPrefix246Batch042', 'BusyBeaver.ZFC.SitesPrefix246Batch043', 'BusyBeaver.ZFC.SitesPrefix246Batch044', 'BusyBeaver.ZFC.SitesPrefix246Batch045', 'BusyBeaver.ZFC.SitesPrefix246Batch046', 'BusyBeaver.ZFC.SitesPrefix246Batch047', 'BusyBeaver.ZFC.SitesPrefix246Batch048', 'BusyBeaver.ZFC.SitesPrefix246Batch049', 'BusyBeaver.ZFC.SitesPrefix246Batch050', 'BusyBeaver.ZFC.SitesPrefix246Batch051', 'BusyBeaver.ZFC.SitesPrefix246Batch052', 'BusyBeaver.ZFC.SitesPrefix246Batch053', 'BusyBeaver.ZFC.SitesPrefix246Batch054', 'BusyBeaver.ZFC.SitesPrefix246Batch055', 'BusyBeaver.ZFC.SitesPrefix246Batch056', 'BusyBeaver.ZFC.SitesPrefix246Batch057', 'BusyBeaver.ZFC.SitesPrefix246Batch058', 'BusyBeaver.ZFC.SitesPrefix246Batch059', 'BusyBeaver.ZFC.SitesPrefix246Batch060', 'BusyBeaver.ZFC.SitesPrefix246Batch061', 'BusyBeaver.ZFC.SitesPrefix246Batch062', 'BusyBeaver.ZFC.SitesPrefix246Batch063', 'BusyBeaver.ZFC.SitesPrefix246Batch064', 'BusyBeaver.ZFC.SitesPrefix246Batch065', 'BusyBeaver.ZFC.SitesPrefix246Batch066', 'BusyBeaver.ZFC.SitesPrefix246Batch067', 'BusyBeaver.ZFC.SitesPrefix246Batch068', 'BusyBeaver.ZFC.SitesPrefix246Batch069', 'BusyBeaver.ZFC.SitesPrefix246Batch070', 'BusyBeaver.ZFC.SitesPrefix246Batch071', 'BusyBeaver.ZFC.SitesPrefix246Batch072', 'BusyBeaver.ZFC.SitesPrefix246Batch073', 'BusyBeaver.ZFC.SitesPrefix246Batch074', 'BusyBeaver.ZFC.SitesPrefix246Batch075', 'BusyBeaver.ZFC.SitesPrefix246Batch076', 'BusyBeaver.ZFC.SitesPrefix246Batch077', 'BusyBeaver.ZFC.SitesPrefix246Batch079', 'BusyBeaver.ZFC.SitesPrefix246Batch080', 'BusyBeaver.ZFC.SitesPrefix246Batch081', 'BusyBeaver.ZFC.SitesPrefix246Batch082', 'BusyBeaver.ZFC.SitesPrefix246Batch083', 'BusyBeaver.ZFC.SitesPrefix246Batch084', 'BusyBeaver.ZFC.SitesPrefix246Batch085', 'BusyBeaver.ZFC.SitesPrefix246Chunk000', 'BusyBeaver.ZFC.SitesPrefix246Chunk041', 'BusyBeaver.ZFC.SitesPrefix246Chunk042', 'BusyBeaver.ZFC.SitesPrefix246Chunk210', 'BusyBeaver.ZFC.SitesPrefix246Join000', 'BusyBeaver.ZFC.SitesPrefix246Join001', 'BusyBeaver.ZFC.SitesPrefix246Join002', 'BusyBeaver.ZFC.SitesPrefix246Join003', 'BusyBeaver.ZFC.SitesPrefix246Join004', 'BusyBeaver.ZFC.SitesPrefix246Join005', 'BusyBeaver.ZFC.SitesPrefix246Join006', 'BusyBeaver.ZFC.SitesPrefix246Join007', 'BusyBeaver.ZFC.SitesPrefix246Join008', 'BusyBeaver.ZFC.SitesPrefix246Join009', 'BusyBeaver.ZFC.SitesPrefix246Join010', 'BusyBeaver.ZFC.SitesPrefix246Join011', 'BusyBeaver.ZFC.SitesPrefix246Join012', 'BusyBeaver.ZFC.SitesPrefix246Join013', 'BusyBeaver.ZFC.SitesPrefix246Join014', 'BusyBeaver.ZFC.SymbolicPrefix246', 'BusyBeaver.ZFC.Table253', 'BusyBeaver.ZFC.TablePerm252', 'BusyBeaver.ZFC.TablePrefix246', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'BusyBeaver.ZFC.TransRec', 'BusyBeaver.ZFC.TupleOrder', 'BusyBeaver.ZFC.WFModel', 'BusyBeaver.ZFC.WFRelativization', 'BusyBeaver.ZFC.WFTheory', 'BusyBeaver.ZFC.WellFoundedPart', 'BusyBeaver.ZFC.WritingRuns', 'BusyBeaver.ZFC.ZFNative', 'BusyBeaver.ZFC.ZFRank', 'BusyBeaver.ZFC.ZipperRuns', 'FirstOrder.Calculus', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf']
PROBES=['blank_initial_config', 'actual_coverage', 'boot_related', 'blank_after_prefix_iff', 'blank_halts_iff_register', 'blank_halts_iff_zf_refutation', 'blank_halts_iff_zfc_refutation', 'nonhalting_iff_zf_consistency', 'nonhalting_iff_zfc_consistency']
TIMEOUT=120
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
for label in PARENTS:p.add_argument('--'+label+'-evidence',type=Path,required=True)
p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled.')
assert all(not h.startswith('PENDING_') for h,m in PARENTS.values()),'Freeze exact successful runtime, complete bootstrap-frame and full-coverage records first.'
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve()
assert not W.is_relative_to(R) and (not W.exists() or not any(W.iterdir()))
S=a.source.resolve() if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryPrefix246.lean'
A=a.audit.resolve() if a.audit else R/'Computability/BusyBeaver/Research/ZFC/binary_prefix246_audit.lean'
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA
imports=lambda q:re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(q).read_text(),re.M)
assert imports(S)==['BusyBeaver.ZFC.RuntimeInstancePrefix246','BusyBeaver.ZFC.BootstrapFrame246','BusyBeaver.ZFC.SitesPrefix246']
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==9
for q in (S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text())
parents={};evidence={};pool={};tool_pool={};candidate_bindings=[];compiler=None
for label,(pin,module) in PARENTS.items():
 E=getattr(a,label+'_evidence').resolve();assert sha(E)==pin
 d=json.loads(E.read_text());parents[label]=d;evidence[str(E)]=pin
 assert d['status']=='PASS' and d['only_standard_axioms'] and d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit']
 assert d['before']==d['after'] and [q['label'] for q in d['commands']]==['source','audit'] and all(q['exit_code']==0 for q in d['commands'])
 assert d['source_object_recorded_before_audit'] and len(d['fresh_modules'])==1
 f=d['fresh_modules'][0];assert f['module']==module and f['source_sha256']==d['source']['sha256']
 if 'source_pass_object' in d:assert d['source_pass_object']==f
 c=d['compiler'];identity=(str(Path(c['path']).resolve()),c['sha256'])
 if compiler is None:compiler=dict(path=identity[0],sha256=identity[1],version=c['version'],compiler_version_query_performed=False)
 else:assert identity==(compiler['path'],compiler['sha256'])
 items=list(d['reused_modules'])+[dict(module=module,source=d['source']['path'],source_sha256=d['source']['sha256'],object=f['path'],object_sha256=f['sha256'])]
 for q in items:
  m=q['module'];row=dict(module=m,source=str(Path(q['source']).resolve()),source_sha256=q['source_sha256'],object=str(Path(q['object']).resolve()),object_sha256=q['object_sha256'],evidence=str(E))
  if m in pool:assert (pool[m]['source_sha256'],pool[m]['object_sha256'])==(row['source_sha256'],row['object_sha256']),m
  else:pool[m]=row
 for q in d['toolchain_providers']:
  m=q['module']
  if m in tool_pool:assert tool_pool[m]['object_sha256']==q['object_sha256']
  else:tool_pool[m]=q
 candidate_bindings.append(dict(label=label,evidence=str(E),fresh_module=module,fresh_object=f,source_object_recorded_before_audit=True))
C=Path(compiler['path']);assert sha(C)==compiler['sha256'];toolroot=C.parent.parent/'lib/lean'
closure=[];visiting=set();tool_names={'Init'}
def visit(m):
 if m in closure:return
 assert m in pool and m not in visiting,m
 visiting.add(m);q=pool[m]
 assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256'],m
 for n in imports(q['source']):
  if n=='Init' or n.startswith(('Lean.','Std.')):tool_names.add(n)
  else:visit(n)
 visiting.remove(m);closure.append(m)
for m in imports(S):visit(m)
assert set(closure)==set(EXPECTED_MODULES) and len(closure)==230
selected={m:pool[m] for m in closure}
parent_summaries=[];parent_snapshots=[]
for row in candidate_bindings:
 module=row['fresh_module'];d=parents[row['label']];used=module in selected
 if used:
  assert sha(d['source']['snapshot'])==sha(d['source']['path'])==d['source']['sha256']
  parent_snapshots.append(Path(d['source']['snapshot']))
 parent_summaries.append(dict(row,fresh_module_selected=used))
W.mkdir(parents=True,exist_ok=True);cache=W/'cache';snap=W/'sources';cache.mkdir()
ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for m in closure:
 dest=cache/Path(m.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(selected[m]['object'])
def first(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 return next(root/rel for root in (cache,toolroot) if (root/rel).is_file())
actual=[]
for m in closure:
 obj=first(m);assert obj.resolve()==Path(selected[m]['object']).resolve() and sha(obj)==selected[m]['object_sha256']
 actual.append(dict(module=m,actual_first=str(obj),resolved=str(obj.resolve()),sha256=sha(obj)))
tools=[]
for m in sorted(tool_names):
 q=tool_pool[m];ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');assert Path(q['object']).resolve()==ref.resolve() and sha(ref)==q['object_sha256']
 obj=first(m);assert obj.resolve()==ref.resolve();tools.append(dict(module=m,object=str(ref),object_sha256=sha(ref),actual_first=str(obj)))
inputs=[Path(__file__).resolve(),S,A,C,ss,aa]+[Path(x) for x in evidence]+parent_snapshots
for q in selected.values():inputs.extend([Path(q['source']),Path(q['object'])])
inputs.extend(Path(q['object']) for q in tools);inputs=list(dict.fromkeys(q.resolve() for q in inputs));before={str(q):sha(q) for q in inputs}
env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',scope=__doc__,prepare_only=a.prepare_only,compiler=compiler,source_overridden=a.source is not None,audit_overridden=a.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=[dict(path=q,sha256=h) for q,h in evidence.items()],parent_summaries=parent_summaries,reused_modules=[selected[m]for m in closure],candidate_provider_count=len(pool),excluded_candidate_modules=sorted(set(pool)-set(closure)),exact_project_import_closure=True,project_module_count=len(closure),toolchain_providers=tools,actual_first_providers=actual,actual_direct_tool_imports=sorted(tool_names),external_project_boundaries=[],before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,shared_wall_seconds=120,limits=dict(threads=1,memory_mebibytes=4096,proof_limits='Lean defaults'))
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(q):sha(q) for q in inputs};assert before==after
 for m in closure:assert sha(first(m))==selected[m]['object_sha256']
 for q in tools:assert sha(first(q['module']))==q['object_sha256']
 r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
deadline=time.monotonic()+TIMEOUT
def run(label,source,obj=None):
 cmd=[str(C),'-j1','-M4096','--root='+str(snap)]
 if obj is not None:cmd+=['-o',str(obj)]
 cmd+=[str(source)];began=time.monotonic();remaining=deadline-began;assert remaining>0
 try:
  cp=subprocess.run(cmd,cwd=snap,env=env,capture_output=True,text=True,timeout=remaining);output,code=cp.stdout+cp.stderr,cp.returncode
 except subprocess.TimeoutExpired as ex:
  dec=lambda x:x.decode(errors='replace') if isinstance(x,bytes) else x or '';output,code=dec(ex.stdout)+dec(ex.stderr)+'\nTIMEOUT\n',-1
 (W/(label+'.log')).write_text(output);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-began,exit_code=code,output=output));save()
 assert code==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,output
 return output
try:
 obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj);assert obj.is_file() and not obj.is_symlink()
 oh=sha(obj);fresh=dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S));r.update(source_object_recorded_before_audit=True,source_pass_object=fresh,fresh_modules=[fresh]);assert first(MODULE).resolve()==obj.resolve();r['fresh_first_provider_before_audit']=dict(module=MODULE,path=str(first(MODULE)),sha256=oh);save()
 out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
 assert [n for n,_ in reports]==[PREFIX+n for n in PROBES]
 assert all({x.strip() for x in a.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for _,a in reports)
 post();assert sha(obj)==oh==sha(first(MODULE));r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=9,callers=9,only_standard_axioms=True,warnings={q['label']:q['output'].count('warning:')for q in r['commands']})
except Exception as ex:
 r.update(status='FAIL',error=str(ex))
 try:post()
 except Exception as e:r['postcheck_error']=str(e)
 save();raise
save();print(W/'verification.json')
