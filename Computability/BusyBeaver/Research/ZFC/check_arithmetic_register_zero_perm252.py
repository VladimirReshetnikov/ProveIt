"""Portable guarded fresh zero-decrement source/audit check.
Successful RegisterDecrement evidence supplies the exact36-project closure.
Only the newsource/audit are freshly checked; no dependency rebuild/download.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time
p=argparse.ArgumentParser(description=__doc__)
for k in ('repo','dependency-root','decrement-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
for k in ('source','audit','cache','lean'):p.add_argument('--'+k,type=Path)
p.add_argument('--library-path',type=Path,action='append',default=[])
p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
if not __debug__:p.error('Assertions must remain enabled; do not use -O.')
R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';s=importlib.util.spec_from_file_location('zero_spare_helpers',helper);H=importlib.util.module_from_spec(s);s.loader.exec_module(H)
records=[(a.decrement_evidence.resolve(),10,12,'6f47bd0a69bf32123aa378cb6c928475bf74eb8254b2b884310809ff1d91e16a','42c40e29cf406f5ea42cb81c555a15512d5fe1621582731a63b7b52be1630b48')]
C,version=H.compiler_path(a.lean);libs,deps=H.dependency_libraries(D,a.library_path);mods={};providers={};old=[];inherited_objects=[]
def source(m):return R/('Logic/FirstOrder/Lean'if m=='FirstOrder.Fol'else'Computability/BusyBeaver/Lean')/Path(m.replace('.','/')).with_suffix('.lean')
def add(q):
 q=dict(q,source=str(source(q['module'])));m=q['module']
 if a.cache:q['object']=str(a.cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))
 assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256'];inherited_objects.append(dict(q))
 if m in mods:assert mods[m]['source_sha256']==q['source_sha256']and mods[m]['object_sha256']==q['object_sha256']
 else:mods[m]=q
for E,probes,callers,ss,aa in records:
 e=json.loads(E.read_text());old.append(e);assert e['status']=='PASS'and e['named_axiom_probes']==probes and e['callers']==callers and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'];assert e['source']['sha256']==ss and e['audit']['sha256']==aa
 assert sha(C)==e['compiler']['sha256']and version==e['compiler']['version']
 for n in ('Foundation','Mathlib'):assert deps[n]['pin']==e['dependencies'][n]['pin']and deps[n]['tracked_clean']and e['dependencies'][n]['tracked_clean']
 assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
 for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
 for q in e['reused_modules']:add(q)
 assert len(e['fresh_modules'])==1;q=e['fresh_modules'][0];assert q['source_sha256']==e['source']['sha256'];add(dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256']))
 for q in e['providers']:
  m=q['module']
  if m in providers:assert providers[m]['source_sha256']==q['source_sha256']and providers[m]['object_sha256']==q['object_sha256']
  else:providers[m]=dict(q)
assert len(mods)==36 and set(providers)=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Arithmetic.Exponential.Exp'}
for m,q in providers.items():
 rel=Path(m.replace('.','/'));dep='Foundation'if m.startswith('Foundation.')else'Mathlib';q['source']=str(Path(deps[dep]['path'])/rel.with_suffix('.lean'));obj=next(p/rel.with_suffix('.olean')for p in libs if(p/rel.with_suffix('.olean')).is_file());assert sha(q['source'])==q['source_sha256']and sha(obj)==q['object_sha256'];q['object']=str(obj.resolve());q['actual_first_provider']=True
S=a.source.resolve()if a.source else R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticRegisterZeroPerm252.lean'
A=a.audit.resolve()if a.audit else R/'Computability/BusyBeaver/Research/ZFC/arithmetic_register_zero_perm252_audit.lean'
assert a.source is not None or sha(S)=='fb0d35d463d9e0142fbfe5ff215e76379a8a9ece127c3e8878a306477cdcb60c'
assert a.audit is not None or sha(A)=='dca0481b18e101eba0c2531672c8bb78cfaaf22c76da364ae5f419010ed8dbd9'
module='BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252';prefix='SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252.'
imports=['BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252'];assert H.lean_imports(S.read_text())==imports and H.lean_imports(A.read_text())==[module]
seen=set();external=set();visiting=set()
def visit(m):
 if m in seen:return
 assert m in mods and m not in visiting;visiting.add(m)
 for n in H.lean_imports(Path(mods[m]['source']).read_text()):
  if n in mods:visit(n)
  else:assert n.startswith(('Foundation.','Mathlib.','Lean.'));external.add(n)
 visiting.remove(m);seen.add(m)
for m in imports:visit(m)
assert seen==set(mods)and external-{n for n in external if n.startswith('Lean.')}<=set(providers)
names=re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M);expected=['restore_zero','return_dec_file','return_zero_prefix','zero_box','file_zero_tail_even','zero_decrement'];assert names==[prefix+n for n in expected]and len(re.findall(r'^example\b',A.read_text(),re.M))==10
cache=W/'cache';cache.mkdir();snap=W/'sources';ss=snap/Path(module.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True);aa=snap/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
for q in mods.values():
 dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
actual=[]
for q in list(mods.values())+list(providers.values()):
 rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(p/rel for p in[cache,*libs]if(p/rel).is_file());assert sha(o)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(o),resolved=str(o.resolve()),sha256=sha(o)))
toolroot=C.parent.parent/'lib/lean';tool=[]
direct_tool_imports={n for f in [S,A]+[Path(q['source'])for q in list(mods.values())+list(providers.values())]for n in H.lean_imports(f.read_text())if n.startswith('Lean.')}
for m in sorted(direct_tool_imports|{'Lean.Elab.Tactic.Omega'}):
 rel=Path(m.replace('.','/')).with_suffix('.olean');ref=toolroot/rel;o=next(p/rel for p in[cache,*libs,toolroot]if(p/rel).is_file());assert sha(o)==sha(ref)
 for e in old:
  for q in e.get('toolchain_providers',[]):
   if q['module']==m:assert sha(o)==q['object_sha256']
 tool.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),actual_first=str(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref),actual_first_provider=True))
inputs=[Path(__file__).resolve(),helper,*[x[0]for x in records],C,S,A,ss,aa,D/'lake-manifest.json']
for q in inherited_objects+list(providers.values()):inputs.extend([Path(q['source']),Path(q['object'])])
inputs.extend(Path(q[k])for q in tool for k in ('object','toolchain_reference'));inputs=list(dict.fromkeys(p.resolve()for p in inputs));before={str(p):sha(p)for p in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,provider_evidence=[dict(path=str(x[0]),sha256=sha(x[0]))for x in records],compiler=dict(path=str(C),version=version,sha256=sha(C)),source_overridden=a.source is not None,audit_overridden=a.audit is not None,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),reused_modules=list(mods.values()),inherited_record_objects=inherited_objects,providers=list(providers.values()),toolchain_providers=tool,actual_direct_tool_imports=sorted(direct_tool_imports),actual_first_providers=actual,exact_project_import_closure=True,dependencies=deps,before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def post():
 after={str(p):sha(p)for p in inputs};assert before==after
 for q in list(mods.values())+list(providers.values())+tool:
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');o=next(p/rel for p in[cache,*libs,toolroot]if(p/rel).is_file());assert sha(o)==q['object_sha256']
 _,d=H.dependency_libraries(D,a.library_path);assert d==deps;r.update(after=after,all_input_provider_postchecks=True)
save()
if a.prepare_only:post();save();print(W/'verification.json');raise SystemExit(0)
def run(label,file,obj=None):
 cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic();cp=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);out=cp.stdout+cp.stderr;(W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=cp.returncode,output=out));save();assert cp.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
try:
 obj=cache/Path(module.replace('.','/')).with_suffix('.olean');run('source',ss,obj);oh=sha(obj);out=run('audit',aa);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==names and all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports);post();assert sha(obj)==oh;r.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,fresh_modules=[dict(module=module,path=str(obj),sha256=oh,source_sha256=sha(S))],module_object=dict(path=str(obj),sha256=oh),named_axiom_probes=6,callers=10,only_standard_axioms=True,warnings=sum(x['output'].count('warning:')for x in r['commands']))
except Exception as ex:r.update(status='FAIL',error=str(ex));save();raise
save();print(W/'verification.json')
