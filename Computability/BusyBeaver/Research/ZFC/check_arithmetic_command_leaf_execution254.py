"""Scoped exact12/12 leaf contract replay from a successful34-import block replay."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time,tempfile
M='BusyBeaver.ZFC.ArithmeticCommandLeafExecution254';N='SetTheory.'+M+'.'
PROBES=[N+n for n in ['eval_nips_cont','select_entry','leaf_contract',*['leaf'+str(i)for i in range(1,9)],'bundle_contract']]
SOURCE=Path('Computability/BusyBeaver/Lean')/Path(M.replace('.','/')).with_suffix('.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_leaf_execution254_audit.lean')
SOURCE_HASH='ddfe71eac3c1d24424877fba56e77a0f428f03393c033d600ecbed6b09e60be6'
AUDIT_HASH='45ae18d44f14f02df82bd1122e799e4f8f03e02316e66ba863b95e5af9f775f4'
EXTERNAL={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def project_source(repo,mod):
 if mod=='FirstOrder.Fol':return repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
 assert mod.startswith('BusyBeaver.ZFC.')
 return repo/'Computability/BusyBeaver/Lean'/Path(mod.replace('.','/')).with_suffix('.lean')
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ('repo','dependency-root','block-evidence'):p.add_argument('--'+key,type=Path,required=True)
 for key in ('source','audit','output','block-cache','alternative-cache','lean'):p.add_argument('--'+key,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();E=a.block_evidence.resolve();e=json.loads(E.read_text())
 assert e['status']=='PASS' and e['named_axiom_probes']==19 and e['callers']==20 and e['only_standard_axioms'] and e['all_input_provider_postchecks']
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('leaf_helpers',helper);h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
 libs,deps=h.dependency_libraries(D,a.library_path)
 for n in ['Foundation','Mathlib']:assert deps[n]['pin']==e['dependencies'][n]['pin'] and deps[n]['tracked_clean']is True and e['dependencies'][n]['tracked_clean']is True
 assert set(deps['providers'])==set(e['dependencies']['providers'])
 for n,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][n]['sha256']
 assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
 C,version=h.compiler_path(a.lean or Path(e['compiler']['path']));assert H(C)==e['compiler']['sha256'] and version==e['compiler']['version']
 rows=[dict(q)for q in e['reused_modules']]+[dict(module='BusyBeaver.ZFC.ArithmeticCommandBlockExecution254',source=e['source']['path'],source_sha256=e['source']['sha256'],object=e['module_object']['path'],object_sha256=e['module_object']['sha256'])]
 assert len(rows)==len({q['module']for q in rows})==35
 for q in rows:
  q['source']=str(project_source(R,q['module']))
  if a.block_cache:q['object']=str(a.block_cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
  assert H(q['source'])==q['source_sha256'] and H(q['object'])==q['object_sha256']
 alternatives=[]
 for old in e.get('same_source_object_alternatives',[]):
  q=dict(old,source=str(project_source(R,old['module'])))
  if a.alternative_cache:q['object']=str(a.alternative_cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
  assert q['module']=='BusyBeaver.ZFC.ArithmeticCantor' and H(q['source'])==q['source_sha256'] and H(q['object'])==q['object_sha256']
  assert q['source_sha256']==next(x['source_sha256']for x in rows if x['module']==q['module'])
  alternatives.append(q)
 known={q['module']:q for q in rows};visited=set();visiting=set();external=set()
 def visit(mod):
  if mod in visited:return
  assert mod in known and mod not in visiting;visiting.add(mod)
  for child in h.lean_imports(Path(known[mod]['source']).read_text()):
   if child in known:visit(child)
   else:assert child.startswith(('Foundation.','Mathlib.'));external.add(child)
  visiting.remove(mod);visited.add(mod)
 visit('BusyBeaver.ZFC.ArithmeticCommandBlockExecution254')
 assert visited==set(known) and external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'}
 providers=[]
 assert {q['module']for q in e['providers']}==EXTERNAL and len(e['providers'])==4
 for q in e['providers']:
  rel=Path(q['module'].replace('.','/'));obj=next(x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file());src=Path(deps['Foundation'if q['module'].startswith('Foundation.')else'Mathlib']['path'])/rel.with_suffix('.lean');assert H(obj)==q['object_sha256'] and H(src)==q['source_sha256'];providers.append(dict(q,source=str(src),object=str(obj.resolve())))
 assert len(providers)==4
 S=a.source.resolve()if a.source else R/SOURCE;A=a.audit.resolve()if a.audit else R/AUDIT
 assert a.source is not None or H(S)==SOURCE_HASH
 assert a.audit is not None or H(A)==AUDIT_HASH
 assert h.lean_imports(S.read_text())==['BusyBeaver.ZFC.ArithmeticCommandBlockExecution254'] and h.lean_imports(A.read_text())==[M]
 assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==PROBES and len(re.findall(r'^example\b',A.read_text(),re.M))==12
 W=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-leaf-execution-'));assert not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snap=W/'sources/BusyBeaver/ZFC';snap.mkdir(parents=True)
 for q in rows:
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 SS=snap/S.name;AA=W/'Audit.lean';shutil.copyfile(S,SS);shutil.copyfile(A,AA)
 files=[Path(__file__).resolve(),helper,C,E,S,A,SS,AA,D/'lake-manifest.json']+[Path(q[k])for q in rows+providers+alternatives for k in ['source','object']];files=list(dict.fromkeys(q.resolve()for q in files));before={str(q):H(q)for q in files};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='All-internal exact fixed eight leaf and bundle contracts. External finite stack notation; no internal source-proof induction or PA endpoint.',source=dict(path=str(S),sha256=H(S)),audit=dict(path=str(A),sha256=H(A)),block_evidence=dict(path=str(E),sha256=H(E)),reused_modules=rows,reused_count=35,same_source_object_alternatives=alternatives,providers=providers,source_override=a.source is not None,audit_override=a.audit is not None,dependencies=deps,compiler=dict(e['compiler'],path=str(C),version=version),before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False)
 def save():(W/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 save()
 def postchecks():
  after={q:H(q)for q in before};assert before==after
  for q in rows:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next((x/rel for x in[cache,*libs]if(x/rel).is_file()),None)
   assert actual and actual.resolve()==Path(q['object']).resolve()and H(actual)==q['object_sha256']
  for q in providers:
   rel=Path(q['module'].replace('.','/')).with_suffix('.olean');actual=next((x/rel for x in libs if(x/rel).is_file()),None)
   assert actual and actual.resolve()==Path(q['object']).resolve()and H(actual)==q['object_sha256']
  _,depafter=h.dependency_libraries(D,a.library_path);assert deps==depafter
  d.update(after=after,all_input_provider_postchecks=True)
 if a.prepare_only:postchecks();save();print(W/'verification.json');return
 def run(label,cmd):
  t=time.monotonic();r=subprocess.run(cmd,cwd=W,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;(W/(label+'.log')).write_text(out);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=out));save();assert r.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 try:
  obj=cache/Path(M.replace('.','/')).with_suffix('.olean');run('source',[str(C),'-M4096','--root='+str(W/'sources'),'-o',str(obj),str(SS)]);oh=H(obj);d['object_immediately_after_source']=dict(path=str(obj),sha256=oh);save();out=run('audit',[str(C),'-M4096',str(AA)])
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==PROBES;assert all(set(x.strip()for x in ax.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
  postchecks();assert H(obj)==oh
  d.update(status='PASS',all_input_provider_postchecks=True,module_object=dict(path=str(obj),sha256=oh),named_axiom_probes=12,callers=12,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[x.strip()for x in ax.split(',')if x.strip()])for n,ax in reports],warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except Exception as ex:d.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
