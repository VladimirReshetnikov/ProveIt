#!/usr/bin/env python3
"""Check only the exact246 arithmetic lookup and its eight-probe/eight-client audit.
Reuse the exact 23-project import closure from checked MP254 and TablePrefix246,
with three existing Foundation/Mathlib boundaries. No dependency rebuild/download,
compiler/version query or proof call during preparation. One thread, 4GiB Lean
memory, default new-source proof limits, shared120s for source plus audit.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
MODULE='BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246.'
SOURCE_SHA='64fc770a13e409f7570bae9e44385c55c7e85b387c86fb55c154aa29b2ff0959'
AUDIT_SHA='5d834ac0f7635e5e47040ffa93eea10cbe6362d35379625a2f4fe68690ba1c03'
MP_SHA='92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b'
TABLE_SHA='70a9a9bfb1546a1c0c6f1503c6261d2d23637dd901e7debec220e7185137ed6d'
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
PROBES=['actionLookup_graph','literalRows_length','literalRows_positive_bounded','actionLookup_bound','literal_lookup_actual','actionLookup_nat','halt_action_number','first_action_number']
EXPECTED_PROJECTS=['BusyBeaver.Core','BusyBeaver.ZFC.FiniteZipper','BusyBeaver.ZFC.TablePerm252','BusyBeaver.ZFC.ArithmeticMachinePerm252','FirstOrder.Fol','BusyBeaver.ZFC.Kalmar','BusyBeaver.ZFC.TarskiCalculus','BusyBeaver.ZFC.TarskiDerived','BusyBeaver.ZFC.TarskiLeibniz','BusyBeaver.ZFC.TarskiClean','BusyBeaver.ZFC.TarskiComplete','BusyBeaver.ZFC.Lukasiewicz','BusyBeaver.ZFC.TarskiFalsity','BusyBeaver.ZFC.Code254','BusyBeaver.ZFC.ArithmeticCantor','BusyBeaver.ZFC.ArithmeticCode254','BusyBeaver.ZFC.ArithmeticTemplates254','BusyBeaver.ZFC.Code254Proof','BusyBeaver.ZFC.Code254History','BusyBeaver.ZFC.ArithmeticRow254','BusyBeaver.ZFC.ArithmeticHistory254','BusyBeaver.ZFC.ArithmeticMachineGraphPerm252','BusyBeaver.ZFC.TablePrefix246']
EXPECTED_BOUNDARIES={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'}
TIMEOUT=120
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--dependency-root',type=Path)
p.add_argument('--mp-evidence',type=Path)
p.add_argument('--table-evidence',type=Path)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve();S=a.source.resolve() if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticMachineGraphPrefix246.lean';A=a.audit.resolve() if a.audit else Path(__file__).resolve().parent/'arithmetic_machine_graph_prefix246_audit.lean'
MP=a.mp_evidence.resolve()if a.mp_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json'
T=a.table_evidence.resolve() if a.table_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/table-prefix246-verification.json';assert sha(MP)==MP_SHA and sha(T)==TABLE_SHA
mp=json.loads(MP.read_text());table=json.loads(T.read_text())
C=Path(mp['compiler']['path']).resolve();version=mp['compiler']['version'];assert C.name=='lean' and sha(C)==mp['compiler']['sha256']
assert version.startswith('Lean (version 4.32.0,')
D=a.dependency_root.resolve()if a.dependency_root else Path(mp['dependencies']['root']).resolve()
assert not W.is_relative_to(R) and not W.is_relative_to(D) and (not W.exists()or not any(W.iterdir()))
assert sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';assert sha(helper)==HELPER_SHA
spec=importlib.util.spec_from_file_location('graph246_existing_arithmetic_policy',helper)
H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
# Never call H.compiler_path: its version subprocess is deliberately excluded.
imports=lambda f:H.lean_imports(Path(f).read_text())
assert imports(S)==['BusyBeaver.ZFC.ArithmeticMachineGraphPerm252','BusyBeaver.ZFC.TablePrefix246']
assert imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]
assert len(re.findall(r'^example\b',A.read_text(),re.M))==8
for f in (S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',f.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',f.read_text())
def passed(d):
 assert d['status']=='PASS' and d['only_standard_axioms']
 assert d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit']
 assert d['source_object_recorded_before_audit']
 assert [x['label']for x in d['commands']]==['source','audit'] and all(x['exit_code']==0 and not x.get('timed_out',False)for x in d['commands'])
 assert d['before']==d['after']
 assert d['compiler']['sha256']==sha(C) and d['compiler']['version']==version
 assert Path(d['compiler']['path']).resolve()==C
 assert len(d['fresh_modules'])==1
 f=d['fresh_modules'][0];assert f['source_sha256']==d['source']['sha256']
 if 'source_pass_object'in d:
  # MP records one additional source_command_index; compare identity fields only.
  assert all(d['source_pass_object'][k]==f[k]for k in ('module','path','sha256','source_sha256'))
passed(mp);passed(table)
assert (mp['named_axiom_probes'],mp['callers'])==(12,22)
assert (table['named_axiom_probes'],table['callers'])==(47,47)
assert table['fresh_modules'][0]['module']=='BusyBeaver.ZFC.TablePrefix246'
# Retain the arithmetic guard's clean pinned dependency and first-provider policy.
libs,deps=H.dependency_libraries(D,[])
def dependency_match(current):
 for name in ('Foundation','Mathlib'):
  assert current[name]['pin']==mp['dependencies'][name]['pin'] and current[name]['tracked_clean'] and mp['dependencies'][name]['tracked_clean']
 assert current['lake_manifest_sha256']==mp['dependencies']['lake_manifest_sha256']
 for name,q in current['providers'].items():assert q['sha256']==mp['dependencies']['providers'][name]['sha256']
dependency_match(deps)
pool={q['module']:dict(q,evidence=str(MP))for q in mp['reused_modules']};assert len(pool)==len(mp['reused_modules'])
for q in table['reused_modules']:
 if q['module']in pool:
  assert all(pool[q['module']][k]==q[k]for k in ('source_sha256','object_sha256'))
f=table['fresh_modules'][0]
pool[f['module']]=dict(module=f['module'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'],evidence=str(T))
external_pool={q['module']:q for q in mp['providers']}
assert len(external_pool)==6
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
for kind in ('source','audit'):
 q=table[kind];assert sha(q['path'])==sha(q['snapshot'])==q['sha256'];parent_snapshots.extend([Path(q['path']),Path(q['snapshot'])])
assert sha(f['path'])==f['sha256']
for m,q in boundaries.items():
 dep='Foundation'if m.startswith('Foundation.')else'Mathlib';s=Path(deps[dep]['path'])/Path(m.replace('.','/')).with_suffix('.lean')
 rel=Path(m.replace('.','/')).with_suffix('.olean');o=next(x/rel for x in libs if(x/rel).is_file())
 assert sha(s)==q['source_sha256'] and sha(o)==q['object_sha256']
 q.update(source=str(s),object=str(o.resolve()),actual_first_provider=True)
 for n in imports(s):
  if is_tool(n):tool_names.add(n)
# Foundation/Mathlib are explicit supplied-cache boundaries, not recursively rebuilt.
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
for m in sorted(tool_names):
 o=first(m);ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');assert o.resolve()==ref.resolve()
 for parent in (mp,table):
  for q in parent.get('toolchain_providers',[]):
   if q['module']==m:assert sha(o)==q['object_sha256']
 tools.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),actual_first=str(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,MP,T,C,S,A,ss,aa,D/'lake-manifest.json',*parent_snapshots]
for q in list(selected.values())+list(boundaries.values()):inputs.extend([Path(q['source']),Path(q['object'])])
for q in tools:inputs.extend([Path(q['object']),Path(q['toolchain_reference'])])
inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):sha(x)for x in inputs}
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,
 compiler=dict(path=str(C),version=version,sha256=sha(C),compiler_version_query_performed=False),
 source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),
 provider_evidence=[dict(path=str(x),sha256=sha(x))for x in (MP,T)],
 parent_selection='Only actual project imports and direct external boundaries are selected; unrelated MP sources/objects and historical same-source alternatives are not imported or rehashed.',
 reused_modules=list(selected.values()),providers=list(boundaries.values()),toolchain_providers=tools,
 actual_first_providers=actual,actual_direct_tool_imports=sorted(tool_names),exact_project_import_closure=True,
 project_module_count=len(selected),external_boundary_count=len(boundaries),dependencies=deps,
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
 r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=8,callers=8,only_standard_axioms=True,
 actual_axiom_sets=[dict(theorem=n,axioms=sorted(s))for(n,_),s in zip(reports,sets)],warnings={q['label']:q['output'].count('warning:')for q in r['commands']})
except Exception as error:
 r.update(status='FAIL',error=str(error))
 try:post()
 except Exception as post_error:r['postcheck_error']=str(post_error)
 save();raise
save();print(W/'verification.json')
