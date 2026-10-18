#!/usr/bin/env python3
"""Check only the seeded arithmetic scheduler and its ten-probe/eleven-client audit.
Reuse exactly 48 imported project modules from EnumeratorEquivalence254, with
three supplied Foundation/Mathlib boundaries. MP254 pins compatible toolchain
objects and cache boundaries; none of its unrelated project modules is imported.
Preparation makes no compiler/version call, dependency build or download.
One thread, 4GiB Lean memory, default proof limits, shared120s source plus audit.
This is an IΣ1 scheduler equivalence, not the actual246 binary comparison.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.ArithmeticEnumeratorSeed246'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246.'
SOURCE_SHA='3e1dbf558880af37d8e6895b8bc9ce02fc90fed0302a3b4a9620d0bdc7a2448e'
AUDIT_SHA='5720c4df76721a0fada4261ce0b3d415f1bf32be91896a3976b75bca8345fc1e'
MP_SHA='92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b'
ENUM_SHA='2aefa3cb2cd415ad03fd055926a8ff8f7f2c27f6a7d60398fb28b21ec42233ca'
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
PROBES=['reach_from', 'halts_of_word_from', 'refutationWord_raw_bound', 'halts_of_accepted_from_three', 'certified_seed_work', 'seed_projections', 'accepted_iff_seed_halts', 'equivalenceSentence_true', 'isigma1_proves_equivalence', 'peano_proves_equivalence']
EXPECTED_PROJECTS=['FirstOrder.Fol', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiLeibniz', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCode254', 'BusyBeaver.ZFC.ArithmeticTemplates254', 'BusyBeaver.ZFC.Code254Proof', 'BusyBeaver.ZFC.Code254History', 'BusyBeaver.ZFC.ArithmeticRow254', 'BusyBeaver.ZFC.ArithmeticHistory254', 'BusyBeaver.ZFC.ArithmeticHistoryRecurrence254', 'BusyBeaver.ZFC.ArithmeticProofConstructors254', 'BusyBeaver.ZFC.ArithmeticStackTail254', 'BusyBeaver.ZFC.ArithmeticStackCertificate254', 'BusyBeaver.ZFC.Enum254', 'BusyBeaver.ZFC.ArithmeticCommandStep254', 'BusyBeaver.ZFC.ArithmeticCommandPreservation254', 'BusyBeaver.ZFC.EnumSafeStart254', 'BusyBeaver.ZFC.EnumStackBarrier254', 'BusyBeaver.ZFC.CommandWord254', 'BusyBeaver.ZFC.ArithmeticCommandWord254', 'BusyBeaver.ZFC.ArithmeticCommandStepWord254', 'BusyBeaver.ZFC.ArithmeticCommandTick254', 'BusyBeaver.ZFC.ArithmeticEnumeratorStep254', 'BusyBeaver.ZFC.ArithmeticCommandRun254', 'BusyBeaver.ZFC.ArithmeticCommandAppend254', 'BusyBeaver.ZFC.ArithmeticCommandWordLaws254', 'BusyBeaver.ZFC.ArithmeticCommandExecution254', 'BusyBeaver.ZFC.ArithmeticEnumeratorRun254', 'BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254', 'BusyBeaver.ZFC.ArithmeticCommandBlocks254', 'BusyBeaver.ZFC.ArithmeticProofWordRow254', 'BusyBeaver.ZFC.ArithmeticProofWord254', 'BusyBeaver.ZFC.ArithmeticProofWordContract254', 'BusyBeaver.ZFC.ArithmeticCommandBlockExecution254', 'BusyBeaver.ZFC.ArithmeticCommandLeafExecution254', 'BusyBeaver.ZFC.ArithmeticCommandRuleExecution254', 'BusyBeaver.ZFC.ArithmeticProofWordCorrect254', 'BusyBeaver.ZFC.ArithmeticRefutationWord254', 'BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254', 'BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254']
EXPECTED_BOUNDARIES={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'}
TIMEOUT=120
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--dependency-root',type=Path)
p.add_argument('--mp-evidence',type=Path)
p.add_argument('--enumerator-evidence',type=Path)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve();S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticEnumeratorSeed246.lean';A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_enumerator_seed246_audit.lean'
MP=a.mp_evidence.resolve()if a.mp_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json'
E=a.enumerator_evidence.resolve()if a.enumerator_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-enumerator-equivalence254-verification.json'
assert sha(MP)==MP_SHA and sha(E)==ENUM_SHA
mp=json.loads(MP.read_text());enum=json.loads(E.read_text())
C=Path(mp['compiler']['path']).resolve();version=mp['compiler']['version'];assert C.name=='lean' and sha(C)==mp['compiler']['sha256']
assert version.startswith('Lean (version 4.32.0,')
D=a.dependency_root.resolve()if a.dependency_root else Path(mp['dependencies']['root']).resolve()
assert not W.is_relative_to(R) and not W.is_relative_to(D) and (not W.exists()or not any(W.iterdir()))
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';assert sha(helper)==HELPER_SHA
spec=importlib.util.spec_from_file_location('seed246_existing_arithmetic_policy',helper)
H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
# Never call H.compiler_path: its version subprocess is deliberately excluded.
imports=lambda f:H.lean_imports(Path(f).read_text())
assert imports(S)==['BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254']
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==11
for f in (S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',f.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',f.read_text())
def passed_common(d):
 assert d['status']=='PASS' and d['only_standard_axioms']
 assert d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit']
 assert all(x['exit_code']==0 and not x.get('timed_out',False)for x in d['commands'])
 assert d['before']==d['after']
 assert d['compiler']['sha256']==sha(C) and d['compiler']['version']==version
 assert Path(d['compiler']['path']).resolve()==C
passed_common(mp);passed_common(enum)
assert [x['label']for x in mp['commands']]==['source','audit']
assert mp['source_object_recorded_before_audit'] and len(mp['fresh_modules'])==1
mf=mp['fresh_modules'][0]
assert all(mp['source_pass_object'][k]==mf[k]for k in ('module','path','sha256','source_sha256'))
assert (mp['named_axiom_probes'],mp['callers'])==(12,22)
# The frozen enumerator record predates the single-source guard schema. Preserve
# its actual four-command order and two fresh objects; do not invent a recorded
# pre-audit object hash field that it does not contain.
assert [x['label']for x in enum['commands']]==[
 'ArithmeticEnumeratorSoundness254Source','ArithmeticEnumeratorSoundness254Audit',
 'ArithmeticEnumeratorEquivalence254Source','ArithmeticEnumeratorEquivalence254Audit']
assert (enum['named_axiom_probes'],enum['callers'])==(14,17)
assert [(q['named_axiom_probes'],q['callers'])for q in enum['new_modules']]==[(9,10),(5,7)]
assert [q['module']for q in enum['fresh_modules']]==[
 'BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254','BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254']
assert [q['module']for q in enum['new_modules']]==[q['module']for q in enum['fresh_modules']]
assert len(enum['reused_modules'])==46
for n,f in zip(enum['new_modules'],enum['fresh_modules']):
 assert f['source_sha256']==n['source']['sha256']
# Retain the arithmetic guard's clean pinned dependency and first-provider policy.
libs,deps=H.dependency_libraries(D,[])
def dependency_match(current):
 for name in ('Foundation','Mathlib'):
  assert current[name]['pin']==mp['dependencies'][name]['pin'] and current[name]['tracked_clean'] and mp['dependencies'][name]['tracked_clean']
 assert current['lake_manifest_sha256']==mp['dependencies']['lake_manifest_sha256']
 assert enum['dependencies']==mp['dependencies']
 for name,q in current['providers'].items():assert q['sha256']==mp['dependencies']['providers'][name]['sha256']
dependency_match(deps)
# Retain the exact objects chosen by the enumerator evidence. Same-source MP
# project alternatives are irrelevant and are not silently substituted.
pool={q['module']:dict(q,evidence=str(E))for q in enum['reused_modules']}
assert len(pool)==46
for f in enum['fresh_modules']:
 assert f['module']not in pool
 pool[f['module']]=dict(module=f['module'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'],evidence=str(E))
assert len(pool)==48
external_pool={q['module']:q for q in enum['providers']}
assert len(external_pool)==4
mp_external={q['module']:q for q in mp['providers']}
for name in EXPECTED_BOUNDARIES:
 assert all(external_pool[name][k]==mp_external[name][k]for k in ('source_sha256','object_sha256'))
selected={};boundaries={};visiting=set();tool_names={'Init'}
is_tool=lambda m:m=='Init'or m.startswith(('Init.','Lean.','Std.'))
def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
def visit(m):
 if m in selected:return
 assert m in pool and m not in visiting;visiting.add(m)
 q=pool[m];s=source(m);o=Path(q['object']).resolve()
 assert sha(s)==q['source_sha256'] and sha(o)==q['object_sha256']
 for n in imports(s):
  if n in pool:visit(n)
  elif is_tool(n):tool_names.add(n)
  else:
   assert n in external_pool and n in EXPECTED_BOUNDARIES;boundaries[n]=dict(external_pool[n])
 visiting.remove(m);selected[m]=dict(module=m,source=str(s),source_sha256=sha(s),object=str(o),object_sha256=sha(o),evidence=q['evidence'])
for name in imports(S):visit(name)
assert list(selected)==EXPECTED_PROJECTS and set(boundaries)==EXPECTED_BOUNDARIES
parent_snapshots=[]
for n,f in zip(enum['new_modules'],enum['fresh_modules']):
 for kind in ('source','audit'):
  q=n[kind];assert sha(q['path'])==sha(q['snapshot'])==q['sha256'];parent_snapshots.extend([Path(q['path']),Path(q['snapshot'])])
 assert sha(f['path'])==f['sha256']
for m,q in boundaries.items():
 dep='Foundation'if m.startswith('Foundation.')else'Mathlib';s=Path(deps[dep]['path'])/Path(m.replace('.','/')).with_suffix('.lean')
 rel=Path(m.replace('.','/')).with_suffix('.olean');o=next(x/rel for x in libs if(x/rel).is_file())
 assert sha(s)==q['source_sha256'] and sha(o)==q['object_sha256']
 q.update(source=str(s),object=str(o.resolve()),actual_first_provider=True)
 for n in imports(s):
  if is_tool(n):tool_names.add(n)
# Foundation/Mathlib are explicit supplied-cache boundaries, not recursively rebuilt.
actual_tool_names=sorted(tool_names);assert actual_tool_names==['Init']
# Explicitly retain MP's matching Omega object as an inherited tool boundary.
tool_names.add('Lean.Elab.Tactic.Omega');toolroot=C.parent.parent/'lib/lean'
W.mkdir(parents=True);cache=W/'cache';snap=W/'sources';cache.mkdir()
ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean'
shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for m,q in selected.items():
 dst=cache/Path(m.replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(q['object'])
paths=[cache,*libs,toolroot]
def first(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 return next(x/rel for x in paths if(x/rel).is_file())
actual=[]
for m,q in {**selected,**boundaries}.items():
 o=first(m);assert o.resolve()==Path(q['object']).resolve() and sha(o)==q['object_sha256']
 actual.append(dict(module=m,actual_first=str(o),resolved=str(o.resolve()),sha256=sha(o)))
tools=[]
assert {q['module']for q in mp['toolchain_providers']}==tool_names
for m in sorted(tool_names):
 o=first(m);ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');assert o.resolve()==ref.resolve()
 for parent in (mp,):
  for q in parent.get('toolchain_providers',[]):
   if q['module']==m:assert sha(o)==q['object_sha256']
 tools.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),actual_first=str(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,MP,E,C,S,A,ss,aa,D/'lake-manifest.json',*parent_snapshots]
for q in list(selected.values())+list(boundaries.values()):inputs.extend([Path(q['source']),Path(q['object'])])
for q in tools:inputs.extend([Path(q['object']),Path(q['toolchain_reference'])])
inputs=list(dict.fromkeys(x.resolve()for x in inputs));assert len(inputs)==122
before={str(x):sha(x)for x in inputs}
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,
 compiler=dict(path=str(C),version=version,sha256=sha(C),compiler_version_query_performed=False),
 source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),
 provider_evidence=[dict(path=str(x),sha256=sha(x))for x in (E,MP)],
 parent_selection='All48 actual project imports come from the exact EnumeratorEquivalence record. MP supplies matching compiler/toolchain/cache-boundary evidence only; none of its unrelated project objects is selected or rehashed. Legacy HFS.Seq is behind the explicit PRF cache boundary, not an additional direct project import.',
 reused_modules=list(selected.values()),providers=list(boundaries.values()),toolchain_providers=tools,
 actual_first_providers=actual,actual_direct_tool_imports=actual_tool_names,inherited_additional_toolchain_boundary='Lean.Elab.Tactic.Omega',exact_project_import_closure=True,
 project_module_count=len(selected),external_boundary_count=len(boundaries),input_count=len(inputs),dependencies=deps,
 before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,
 source_object_recorded_before_audit=False,per_command_timeout_seconds=TIMEOUT,shared_wall_seconds=TIMEOUT,
 limits=dict(threads=1,memory_mebibytes=4096,proof_limits='Lean defaults for new source/audit',shared_source_audit_seconds=TIMEOUT))
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(x):sha(x)for x in inputs};assert after==before
 for m,q in {**selected,**boundaries}.items():assert first(m).resolve()==Path(q['object']).resolve() and sha(first(m))==q['object_sha256']
 for q in tools:assert first(q['module']).resolve()==Path(q['toolchain_reference']).resolve() and sha(first(q['module']))==q['object_sha256']
 _,now=H.dependency_libraries(D,[]);dependency_match(now);assert now==deps
 r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:
 post();save();print(W/'verification.json');raise SystemExit(0)
deadline=time.monotonic()+TIMEOUT
def run(label,path,obj=None):
 cmd=[str(C),'-j1','-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(path)]
 began=time.monotonic();remaining=deadline-began;assert remaining>0,'Shared source/audit wall budget exhausted.'
 timed_out=False
 try:
  cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True,timeout=remaining);output=cp.stdout+cp.stderr;code=cp.returncode
 except subprocess.TimeoutExpired as ex:
  def decoded(x):return x.decode(errors='replace')if isinstance(x,bytes)else(x or'')
  output=decoded(ex.stdout)+decoded(ex.stderr)+'\nTIMEOUT\n';code=-1;timed_out=True
 (W/(label+'.log')).write_text(output)
 r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-began,exit_code=code,timed_out=timed_out,output=output));save()
 assert code==0 and 'sorryAx'not in output and "declaration uses 'sorry'"not in output,output
 return output
try:
 obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj)
 assert obj.is_file() and not obj.is_symlink();oh=sha(obj);fresh=dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S))
 assert first(MODULE).resolve()==obj.resolve()
 r.update(source_object_recorded_before_audit=True,source_pass_object=dict(fresh,source_command_index=0),fresh_modules=[fresh],fresh_first_provider_before_audit=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE))))
 save();out=run('audit',aa)
 reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
 assert [n for n,_ in reports]==[PREFIX+n for n in PROBES]
 sets=[{x.strip()for x in ax.split(',')if x.strip()}for _,ax in reports]
 assert all(x<={'propext','Classical.choice','Quot.sound'}for x in sets)
 post();assert sha(obj)==oh and first(MODULE).resolve()==obj.resolve() and sha(first(MODULE))==oh
 r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=10,callers=11,only_standard_axioms=True,
 actual_axiom_sets=[dict(theorem=n,axioms=sorted(s))for(n,_),s in zip(reports,sets)],warnings={q['label']:q['output'].count('warning:')for q in r['commands']})
except Exception as error:
 r.update(status='FAIL',error=str(error))
 try:post()
 except Exception as post_error:r['postcheck_error']=str(post_error)
 save();raise
save();print(W/'verification.json')
