#!/usr/bin/env python3
"""Strict sequential arithmetic246 source/audit check against pinned successful parents.
Exact project import DFS and explicit supplied Foundation/Mathlib boundaries;
no dependency build/download, version query, or proof call during preparation.
One thread, 4096 MiB, shared120s and default new-source/audit proof limits.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
CFG = {'module': 'BusyBeaver.ZFC.ArithmeticBootstrapPrefix246',
 'source': {'path': 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticBootstrapPrefix246.lean',
            'sha256': 'c942dc0c51d1963e0f54fd2bba2415e2f4816d78f54b6c3e6d3655ae6524b481'},
 'audit': {'path': 'Computability/BusyBeaver/Research/ZFC/arithmetic_bootstrap_prefix246_audit.lean',
           'sha256': '2794e77ca2ad70e462691d33dde4b77f93d6e4208926d765ffec9d8ab38687f9'},
 'parents': {'run': {'module': 'BusyBeaver.ZFC.ArithmeticMachineRunPrefix246',
                     'default': 'Computability/BusyBeaver/Research/ZFC/results/arithmetic-machine-run-prefix246-verification.json',
                     'sha256': 'e531e7cd2313988da8c01809a4a5a4802acdfbb0debb93bfe2cb7b9d8b0f71a4',
                     'audit_census': [14, 16]},
             'bootstrap': {'module': 'BusyBeaver.ZFC.BootPrefix246Chunk008',
                           'default': 'Computability/BusyBeaver/Research/ZFC/bootstrap-prefix246/attempts/group08/run1/verification.json',
                           'sha256': 'a0edda1d5159aedc681950fb27ceaaad9c9bdd93aa3e879011272f0fcc7fbc9f',
                           'audit_census': [9, 9]}},
 'direct_imports': ['BusyBeaver.ZFC.ArithmeticMachineRunPrefix246',
                    'BusyBeaver.ZFC.ArithmeticBootstrapPerm252',
                    'BusyBeaver.ZFC.BootPrefix246Chunk008'],
 'expected_projects': ['BusyBeaver.Core',
                       'BusyBeaver.ZFC.FiniteZipper',
                       'BusyBeaver.ZFC.TablePerm252',
                       'BusyBeaver.ZFC.ArithmeticMachinePerm252',
                       'FirstOrder.Fol',
                       'BusyBeaver.ZFC.Kalmar',
                       'BusyBeaver.ZFC.TarskiCalculus',
                       'BusyBeaver.ZFC.TarskiDerived',
                       'BusyBeaver.ZFC.TarskiLeibniz',
                       'BusyBeaver.ZFC.TarskiClean',
                       'BusyBeaver.ZFC.TarskiComplete',
                       'BusyBeaver.ZFC.Lukasiewicz',
                       'BusyBeaver.ZFC.TarskiFalsity',
                       'BusyBeaver.ZFC.Code254',
                       'BusyBeaver.ZFC.ArithmeticCantor',
                       'BusyBeaver.ZFC.ArithmeticCode254',
                       'BusyBeaver.ZFC.ArithmeticTemplates254',
                       'BusyBeaver.ZFC.Code254Proof',
                       'BusyBeaver.ZFC.Code254History',
                       'BusyBeaver.ZFC.ArithmeticRow254',
                       'BusyBeaver.ZFC.ArithmeticHistory254',
                       'BusyBeaver.ZFC.ArithmeticMachineGraphPerm252',
                       'BusyBeaver.ZFC.ArithmeticMachineStepPerm252',
                       'BusyBeaver.ZFC.TablePrefix246',
                       'BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246',
                       'BusyBeaver.ZFC.ArithmeticMachineStepPrefix246',
                       'BusyBeaver.ZFC.ArithmeticMachineRunPrefix246',
                       'BusyBeaver.ZFC.ArithmeticMachineRunPerm252',
                       'BusyBeaver.ZFC.BootPerm252',
                       'BusyBeaver.ZFC.ArithmeticBootstrapPerm252',
                       'BusyBeaver.ZFC.FastTablePrefix246',
                       'BusyBeaver.ZFC.BootPrefix246First',
                       'BusyBeaver.ZFC.BootPrefix246Chunk001',
                       'BusyBeaver.ZFC.BootPrefix246Chunk002',
                       'BusyBeaver.ZFC.BootPrefix246Chunk003',
                       'BusyBeaver.ZFC.BootPrefix246Chunk004',
                       'BusyBeaver.ZFC.BootPrefix246Chunk005',
                       'BusyBeaver.ZFC.BootPrefix246Chunk006',
                       'BusyBeaver.ZFC.BootPrefix246Chunk007',
                       'BusyBeaver.ZFC.BootPrefix246Probe16384',
                       'BusyBeaver.ZFC.BootPrefix246Chunk008'],
 'expected_boundaries': ['Foundation.FirstOrder.Arithmetic.IOpen.Basic',
                         'Mathlib.Tactic.Ring',
                         'Foundation.FirstOrder.Arithmetic.HFS.PRF',
                         'Foundation.FirstOrder.Arithmetic.Definability.Absoluteness'],
 'probes': ['SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.standard_boot',
            'SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.run_cast',
            'SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.internal_boot',
            'SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.runEquationSentence_eval',
            'SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.bootstrapSentence_true',
            'SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.isigma1_proves_bootstrap',
            'SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246.peano_proves_bootstrap'],
 'callers': 9,
 'scope': 'Exact410735 whole-tape bootstrap transported to every ISigma1 model and a provable finite arithmetic '
          'sentence; no arbitrary internal runtime comparison.'}
MP_SHA='92c2bddc7390806e81b30daa15c2bcfe082dcae6555392a57fe6d1ae987df81b'
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
TIMEOUT=120
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--dependency-root',type=Path)
p.add_argument('--mp-evidence',type=Path)
for label,row in CFG['parents'].items():p.add_argument('--'+label+'-evidence',type=Path)
p.add_argument('--source',type=Path)
p.add_argument('--audit',type=Path)
p.add_argument('--prepare-only',action='store_true')
a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
assert all(not row['sha256'].startswith('PENDING_')for row in CFG['parents'].values()),'Freeze exact predecessor PASS before preparation.'
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
R=a.repo.resolve();W=a.output.resolve();S=a.source.resolve()if a.source else R/CFG['source']['path'];A=a.audit.resolve()if a.audit else R/CFG['audit']['path']
MP=a.mp_evidence.resolve()if a.mp_evidence else R/'Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json'
assert sha(MP)==MP_SHA;mp=json.loads(MP.read_text())
C=Path(mp['compiler']['path']).resolve();version=mp['compiler']['version'];assert C.name=='lean'and sha(C)==mp['compiler']['sha256']
assert version.startswith('Lean (version 4.32.0,')
D=a.dependency_root.resolve()if a.dependency_root else Path(mp['dependencies']['root']).resolve()
assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()))
assert sha(S)==CFG['source']['sha256']and sha(A)==CFG['audit']['sha256']
helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';assert sha(helper)==HELPER_SHA
spec=importlib.util.spec_from_file_location('arithmetic246_existing_dependency_policy',helper)
H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
# H.compiler_path queries --version and must not be called.
imports=lambda f:H.lean_imports(Path(f).read_text())
MODULE=CFG['module'];PROBES=CFG['probes'];CALLERS=CFG['callers']
assert imports(S)==CFG['direct_imports']and imports(A)==[MODULE]
assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==PROBES
assert len(re.findall(r'^example\b',A.read_text(),re.M))==CALLERS
for f in(S,A):
 assert not re.search(r'\b(sorry|admit|native_decide)\b',f.read_text())
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',f.read_text())
def passed(d):
 assert d['status']=='PASS'and d['only_standard_axioms']
 assert d['all_input_provider_postchecks']and d['all_fresh_objects_unchanged_after_audit']
 assert d['source_object_recorded_before_audit']and d['before']==d['after']
 assert [q['label']for q in d['commands']]==['source','audit']and all(q['exit_code']==0 and not q.get('timed_out',False)for q in d['commands'])
 assert Path(d['compiler']['path']).resolve()==C and d['compiler']['sha256']==sha(C)and d['compiler']['version']==version
 assert len(d['fresh_modules'])==1
 f=d['fresh_modules'][0];assert f['source_sha256']==d['source']['sha256']
 if 'source_pass_object'in d:assert all(d['source_pass_object'][k]==f[k]for k in('module','path','sha256','source_sha256'))
passed(mp);assert(mp['named_axiom_probes'],mp['callers'])==(12,22)
libs,deps=H.dependency_libraries(D,[])
def dependency_match(current):
 for name in('Foundation','Mathlib'):
  assert current[name]['pin']==mp['dependencies'][name]['pin']and current[name]['tracked_clean']and mp['dependencies'][name]['tracked_clean']
 assert current['lake_manifest_sha256']==mp['dependencies']['lake_manifest_sha256']
 for name,q in current['providers'].items():assert q['sha256']==mp['dependencies']['providers'][name]['sha256']
dependency_match(deps)
pool={};external_pool={q['module']:q for q in mp['providers']};evidence={str(MP):MP_SHA};parents=[mp];parent_snapshots=[];parent_summaries=[]
def add_provider(q,record):
 m=q['module'];row=dict(module=m,source=str(Path(q['source']).resolve()),source_sha256=q['source_sha256'],object=str(Path(q['object']).resolve()),object_sha256=q['object_sha256'],evidence=str(record))
 if m in pool:assert all(pool[m][k]==row[k]for k in('source_sha256','object_sha256')),m
 else:pool[m]=row
for q in mp['reused_modules']:add_provider(q,MP)
for label,pin in CFG['parents'].items():
 override=getattr(a,label+'_evidence');E=override.resolve()if override else R/pin['default'];assert sha(E)==pin['sha256'];d=json.loads(E.read_text());passed(d);parents.append(d);evidence[str(E)]=pin['sha256']
 f=d['fresh_modules'][0];assert f['module']==pin['module']
 assert(d['named_axiom_probes'],d['callers'])==tuple(pin['audit_census'])
 for q in d['reused_modules']:add_provider(q,E)
 add_provider(dict(module=f['module'],source=d['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256']),E)
 for q in d.get('providers',[]):
  assert q['module']in external_pool
  assert all(external_pool[q['module']][k]==q[k]for k in('source_sha256','object_sha256'))
 for kind in('source','audit'):
  q=d[kind];assert sha(q['path'])==sha(q['snapshot'])==q['sha256'];parent_snapshots.extend([Path(q['path']),Path(q['snapshot'])])
 assert sha(f['path'])==f['sha256']
 parent_summaries.append(dict(label=label,evidence=str(E),module=f['module'],source_sha256=f['source_sha256'],object_sha256=f['sha256'],source_object_recorded_before_audit=True))
selected={};boundaries={};visiting=set();tool_names={'Init'}
is_tool=lambda m:m=='Init'or m.startswith(('Init.','Lean.','Std.'))
def visit(m):
 if m in selected:return
 assert m in pool and m not in visiting,m;visiting.add(m)
 q=pool[m];s=Path(q['source']);o=Path(q['object']);assert sha(s)==q['source_sha256']and sha(o)==q['object_sha256'],m
 for n in imports(s):
  if n in pool:visit(n)
  elif is_tool(n):tool_names.add(n)
  else:assert n in external_pool and n in CFG['expected_boundaries'];boundaries[n]=dict(external_pool[n])
 visiting.remove(m);selected[m]=q
for m in imports(S):visit(m)
assert list(selected)==CFG['expected_projects']and set(boundaries)==set(CFG['expected_boundaries'])
for m,q in boundaries.items():
 dep='Foundation'if m.startswith('Foundation.')else'Mathlib';s=Path(deps[dep]['path'])/Path(m.replace('.','/')).with_suffix('.lean')
 rel=Path(m.replace('.','/')).with_suffix('.olean');o=next(root/rel for root in libs if(root/rel).is_file())
 assert sha(s)==q['source_sha256']and sha(o)==q['object_sha256'];q.update(source=str(s),object=str(o.resolve()),actual_first_provider=True)
 for n in imports(s):
  if is_tool(n):tool_names.add(n)
# Direct external providers are explicit supplied-cache boundaries; no recursive rebuild.
tool_names.add('Lean.Elab.Tactic.Omega');toolroot=C.parent.parent/'lib/lean'
W.mkdir(parents=True);cache=W/'cache';snap=W/'sources';cache.mkdir()
ss=snap/Path(MODULE.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for m,q in selected.items():
 dst=cache/Path(m.replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(q['object'])
paths=[cache,*libs,toolroot]
def first(m):
 rel=Path(m.replace('.','/')).with_suffix('.olean');return next(root/rel for root in paths if(root/rel).is_file())
actual=[]
for m,q in{**selected,**boundaries}.items():
 o=first(m);assert o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'];actual.append(dict(module=m,actual_first=str(o),resolved=str(o.resolve()),sha256=sha(o)))
tools=[]
for m in sorted(tool_names):
 o=first(m);ref=toolroot/Path(m.replace('.','/')).with_suffix('.olean');assert o.resolve()==ref.resolve()
 for parent in parents:
  for q in parent.get('toolchain_providers',[]):
   if q['module']==m:assert sha(o)==q['object_sha256']
 tools.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),actual_first=str(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,C,S,A,ss,aa,D/'lake-manifest.json',*map(Path,evidence),*parent_snapshots]
for q in list(selected.values())+list(boundaries.values()):inputs.extend([Path(q['source']),Path(q['object'])])
for q in tools:inputs.extend([Path(q['object']),Path(q['toolchain_reference'])])
inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):sha(x)for x in inputs}
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=CFG['scope'],prepare_only=a.prepare_only,
 compiler=dict(path=str(C),version=version,sha256=sha(C),compiler_version_query_performed=False),
 source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),
 provider_evidence=[dict(path=path,sha256=h)for path,h in evidence.items()],parent_summaries=parent_summaries,
 parent_selection='Only actual import DFS projects and direct external boundaries; unrelated MP objects are not imported or rehashed.',
 reused_modules=list(selected.values()),providers=list(boundaries.values()),toolchain_providers=tools,actual_first_providers=actual,actual_direct_tool_imports=sorted(tool_names),
 exact_project_import_closure=True,project_module_count=len(selected),external_boundary_count=len(boundaries),dependencies=deps,
 before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,source_object_recorded_before_audit=False,
 per_command_timeout_seconds=TIMEOUT,shared_wall_seconds=TIMEOUT,limits=dict(threads=1,memory_mebibytes=4096,proof_limits='Lean defaults for new source/audit',shared_source_audit_seconds=TIMEOUT))
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(x):sha(x)for x in inputs};assert after==before
 for m,q in{**selected,**boundaries}.items():assert first(m).resolve()==Path(q['object']).resolve()and sha(first(m))==q['object_sha256']
 for q in tools:assert first(q['module']).resolve()==Path(q['toolchain_reference']).resolve()and sha(first(q['module']))==q['object_sha256']
 _,now=H.dependency_libraries(D,[]);dependency_match(now);assert now==deps;r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
deadline=time.monotonic()+TIMEOUT
def run(label,path,obj=None):
 cmd=[str(C),'-j1','-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(path)]
 began=time.monotonic();remaining=deadline-began;assert remaining>0,'Shared source/audit wall budget exhausted.';timed_out=False
 try:
  cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True,timeout=remaining);output=cp.stdout+cp.stderr;code=cp.returncode
 except subprocess.TimeoutExpired as ex:
  decoded=lambda x:x.decode(errors='replace')if isinstance(x,bytes)else(x or'');output=decoded(ex.stdout)+decoded(ex.stderr)+'\nTIMEOUT\n';code=-1;timed_out=True
 (W/(label+'.log')).write_text(output);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-began,exit_code=code,timed_out=timed_out,output=output));save()
 assert code==0 and 'sorryAx'not in output and "declaration uses 'sorry'"not in output,output
 return output
try:
 obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',ss,obj);assert obj.is_file()and not obj.is_symlink();oh=sha(obj);fresh=dict(module=MODULE,path=str(obj),sha256=oh,source_sha256=sha(S))
 assert first(MODULE).resolve()==obj.resolve();r.update(source_object_recorded_before_audit=True,source_pass_object=dict(fresh,source_command_index=0),fresh_modules=[fresh],fresh_first_provider_before_audit=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE))));save()
 out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
 assert[n for n,_ in reports]==PROBES
 sets=[{x.strip()for x in ax.split(',')if x.strip()}for _,ax in reports];assert all(x<={'propext','Classical.choice','Quot.sound'}for x in sets)
 post();assert sha(obj)==oh and first(MODULE).resolve()==obj.resolve()and sha(first(MODULE))==oh
 r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=len(PROBES),callers=CALLERS,only_standard_axioms=True,
  actual_axiom_sets=[dict(theorem=n,axioms=sorted(s))for(n,_),s in zip(reports,sets)],warnings={q['label']:q['output'].count('warning:')for q in r['commands']})
except Exception as error:
 r.update(status='FAIL',error=str(error))
 try:post()
 except Exception as post_error:r['postcheck_error']=str(post_error)
 save();raise
save();print(W/'verification.json')
