#!/usr/bin/env python3
"""Run actual 22-source wrapper logic with synthetic audited inputs and fake children."""
import contextlib,hashlib,importlib.util,json,os,re,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;RUN=HERE/'replay.py'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise ValueError(msg)
need(__debug__ and not sys.flags.optimize,'optimized Python rejected')
FAKE='''#!/usr/bin/python3
import os,re,sys
from pathlib import Path
root=Path(FAKE_ROOT);mode=(root/'mode').read_text();args=sys.argv[1:];lib,pkg=map(Path,os.environ['LEAN_PATH'].split(':'))
if '--deps' in args:
 src=Path(args[-1]);names=['Init']+re.findall(r'^import\\s+([\\w.]+)',src.read_text(),re.M)
 for dep in names:
  rel=Path(*dep.split('.')).with_suffix('.olean');hits=[p for p in (lib/rel,pkg/rel) if p.is_file()]
  if not hits:sys.exit(12)
  print(hits[0])
 if mode=='wrong-deps':print(root/'bad.olean')
 sys.exit(0)
src=Path(next(x for x in args if x.endswith('.lean')));out=Path(args[args.index('-o')+1]);count=root/'count';n=int(count.read_text())+1 if count.exists() else 1;count.write_text(str(n));out.parent.mkdir(parents=True,exist_ok=True)
if mode=='nonzero' and n==2:sys.exit(8)
if mode=='shadow-object' and n==1:(lib/'Init.olean').write_bytes(b'shadow')
if mode=='shadow-companion' and n==1:(lib/'Init.olean.private').write_bytes(b'shadow')
if mode=='package-companion' and n==1:(pkg/'Init.olean.private').write_bytes(b'extra')
if mode=='old-object-mutate' and n==2:(lib/'DiophantineConsistency/CompactPermutationInterface.olean').write_bytes(b'changed')
if mode=='late-source-mutate' and n==3:(src.parent/'CompactPermutationInterface.lean').write_text('changed')
if mode=='final-source-mutate' and n==22:(src.parent/'CompactPermutationInterface.lean').write_text('changed')
if mode=='final-shadow-companion' and n==22:(lib/'Init.olean.private').write_bytes(b'late')
if mode=='final-old-object-mutate' and n==22:(lib/'DiophantineConsistency/CompactPermutationInterface.olean').write_bytes(b'late')
if mode=='identical-source-symlink' and n==2:
 p=src.parent/'CompactPermutationInterface.lean';t=root/'same-source';t.write_bytes(p.read_bytes());p.unlink();p.symlink_to(t)
if mode=='redirect-directory' and n==1:
 old=out.parent;old.rename(root/'saved-project');(root/'outside').mkdir();old.symlink_to(root/'outside',target_is_directory=True)
if mode=='symlink-output' and n==1:
 target=root/'outside-output';target.write_bytes(b'object');out.symlink_to(target)
elif mode!='missing-output' or n!=1:out.write_bytes(('fake-object-'+str(n)).encode())
if mode=='output-companion' and n==1:Path(str(out)+'.private').write_bytes(b'extra')
if mode=='warning' and n==1:print(str(src)+':1:1: warning: injected')
if mode in ('all-known-warnings','strip-changed-warning','soundness-changed-warning','strip-extra-output') and n in (7,16,18):
 text=FAKE_BASELINES['DiophantineConsistency.'+src.stem].replace('<SOURCE>',str(src))
 if (mode=='strip-changed-warning' and n==16) or (mode=='soundness-changed-warning' and n==18):text=text.replace('warning:','warning: changed',1)
 if mode=='strip-extra-output' and n==16:text+='extra output\\n'
 print(text,end='')
if mode in ('plane-warning','plane-extra-warning','plane-changed-warning','plane-warning-wrong-path','plane-warning-sorry') and n==7:
 for line,col in ((252,24),(276,46)):
  path=str(src) if mode!='plane-warning-wrong-path' else '/tmp/not-the-source.lean'
  print(path+':'+str(line)+':'+str(col)+": warning: `mul_le_mul_left'` has been deprecated: Use `_root_.mul_le_mul_right` instead"+(' modified' if mode=='plane-changed-warning' and line==252 else ''))
 if mode=='plane-extra-warning':print(str(src)+':1:1: warning: injected')
 if mode=='plane-warning-sorry':print('sorryAx')
names=re.findall(r'^#print\\s+axioms\\s+([\\w.]+)\\s*$',src.read_text(),re.M)
for name in names:
 if mode=='missing-report' and n==1:continue
 ax='Unexpected.axiom' if mode=='extra-axiom' and n==1 else 'propext'
 print("'"+name+"' depends on axioms: ["+ax+"]")
 if mode=='duplicate-report' and n==1:print("'"+name+"' depends on axioms: [propext]")
'''
MON='''import os,subprocess
from pathlib import Path
def overlay(base,dest):
 for root,dirs,files in os.walk(base,followlinks=False):
  root=Path(root);target=dest/root.relative_to(base);target.mkdir(parents=True,exist_ok=True)
  for name in files:(target/name).symlink_to((root/name).resolve())
def monitored(cmd,env,log,timeout=600):
 with log.open('x') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
 return r.returncode,123456,None
'''
modes=['success','all-known-warnings','strip-changed-warning','soundness-changed-warning','strip-extra-output','plane-warning','plane-extra-warning','plane-changed-warning','plane-warning-wrong-path','plane-warning-sorry','shadow-object','shadow-companion','package-companion','old-object-mutate','late-source-mutate','redirect-directory','symlink-output','missing-output','output-companion','nonzero','warning','wrong-deps','missing-report','extra-axiom','duplicate-report','identical-source-symlink','final-source-mutate','final-shadow-companion','final-old-object-mutate','audit-before-failure','audit-after-failure','prior-scan-drift','closure-check-drift','reviewed-source-drift','reviewed-candidate-drift','closure-schema-failure']
actual=json.loads((HERE.parent/'compact44-marked-suffix-corrected-source-plan/source-scan.json').read_text())['sources'];need(len(actual)==22,'real source count')
with tempfile.TemporaryDirectory(prefix='marked-suffix-full-fake-') as tmp:
 root=Path(tmp);results={}
 for mode in modes:
  case=root/mode;case.mkdir();repo=case/'repo';repo.mkdir();plan=case/'plan';plan.mkdir();prior=case/'prior';prior.mkdir();audit=case/'audit';audit.mkdir();parent=case/'parent';parent.mkdir();seed=case/'seed';seed.mkdir();pkg=case/'package';pkg.mkdir();(pkg/'Init.olean').write_bytes(b'fake-init')
  spec=importlib.util.spec_from_file_location('marked_runner_'+mode.replace('-','_'),RUN);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
  rows=[]
  for x in actual:
   path=repo/'sources'/(x['module'].split('.')[-1]+'.lean');path.parent.mkdir(exist_ok=True);path.write_bytes(Path(x['source']).read_bytes());rows.append({'module':x['module'],'source':str(path),'sha256':H(path),'imports':x['imports']})
  priorrows=[]
  for r in rows[:18]:priorrows.append({'module':r['module'],'source':str(Path(r['source']).relative_to(repo)),'sha256':r['sha256']})
  busy=prior/'busybeaver-source-scan.json';busy.write_text(json.dumps({'ordered_sources':[{'module':'dummy'} for _ in range(82)]}));prev=prior/'source-scan.json';prev.write_text(json.dumps({'ordered_sources':priorrows}));
  names={r['module'] for r in rows};direct=set()
  for r in rows:
   for dep in ['Init']+r['imports']:
    if dep not in names:direct.add(dep)
  for dep in direct-{'Init'}:
   obj=(seed/Path(*dep.split('.'))).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(('seed-'+dep).encode())
  candidates={}
  for dep in direct:
   cs=[]
   for d in (seed,pkg):
    stem=d/Path(*dep.split('.'));cs.append({'root':str(d),'object':mod.rec(Path(str(stem)+'.olean')),'slots':mod.slots(stem)})
   candidates[dep]={'chosen_root':next(c['root'] for c in cs if c['object'] is not None),'candidates':cs}
  scan=plan/'source-scan.json';scan.write_text(json.dumps({'status':'PASS_SOURCE_ONLY_SUFFIX_SCAN','sources':rows,'direct_candidates':candidates}));ps=plan/'scan.py';ps.write_text('fake scan')
  closure=audit/'CHECK.json';closure.write_text(json.dumps({'status':'PASS_NO_LEAN_CORRECTED_MARKED_SUFFIX_SOURCE_REVIEW','reviewed_commit':'7fd9b953f9','scan_sha256':H(scan),'source_count':22,'changed_position':21,'direct_modules':26,'candidate_slots':520,'target_slots':440,'prior_inventories_equal':True,'lean_launched':False,'author_scan_rerun_exit':0,'optimized_scan_exit':1,'isolated_source_sha256':'6d98a5ac6a8d892e2b6ee5e9fa908d276a52311cb4647a1a05350470f59ffcf2','isolated_log_sha256':'30bddd6fecc5844fbc4602d711d0bdaa1bad4a5e88854efbaca7764b8a58f06e','parent_review_reruns':{'compact44-marked-halt-client-mathematical-review':{'check_sha256':'cdbfc57c65270e10d5265a137ec1dac5bbd872b34bbdb29cf79949aec28c702c','exit':0},'compact44-marked-suffix-source-independent-review':{'check_sha256':'91ed365da479a7ce7fe2e83651cfba486e8e5aa2a01ec6c055c7bca85640750e','exit':0}}}))
  for d in (audit,parent):
   (d/'terminal-observation.json').write_text('{}');(d/'audit.py').write_text('fake')
  seedresult=case/'seed-result.json';seedresult.write_text(json.dumps({'status':'PASS_AUTHOR_ONLY_CHUNKED_TABLE','steps':[{}]*96}));(parent/'CHECK.json').write_text(json.dumps({'status':'PASS_INDEPENDENT_AUTHOR_ONLY_WANG_ARTIFACT_AUDIT','result_sha256':H(seedresult)}))
  mon=case/'monitor.py';mon.write_text(MON);lean=case/'fake-lean';lean.write_text(FAKE.replace('FAKE_ROOT',repr(str(case))).replace('FAKE_BASELINES',repr(mod.warning_baseline())));lean.chmod(0o755);(case/'mode').write_text(mode)
  mod.REPO=repo;mod.PLAN=plan;mod.PRIOR=prior;mod.AUDIT=audit;mod.PARENT=parent;mod.SEED=seed;mod.PKG=pkg;mod.SEED_RESULT=seedresult;mod.MON=mon;mod.LEAN=lean
  mod.PINS={'history_state':H(mod.HIST/'state.json'),'history_log':H(mod.HIST/'logs/DiophantineConsistency_ArithmeticWangPlane-attempt-1.log'),'plan_scan':H(scan),'plan_script':H(ps),'prior_source':H(prev),'prior_busy':H(busy),'closure_check':H(closure),'closure_terminal':H(audit/'terminal-observation.json'),'closure_audit':H(audit/'audit.py'),'parent_check':H(parent/'CHECK.json'),'parent_terminal':H(parent/'terminal-observation.json'),'parent_audit':H(parent/'audit.py'),'seed_result':H(seedresult),'monitor':H(mon),'lean':H(lean)}
  if mode=='prior-scan-drift':prev.write_text('changed')
  if mode=='closure-check-drift':closure.write_text('changed')
  if mode=='reviewed-source-drift':Path(rows[0]['source']).write_text('changed')
  if mode=='reviewed-candidate-drift':
   dep=next(x for x in direct if x!='Init');(seed/Path(*dep.split('.'))).with_suffix('.olean').write_bytes(b'changed')
  if mode=='closure-schema-failure':
   bad=json.loads(closure.read_text());bad['lean_launched']=True;closure.write_text(json.dumps(bad));mod.PINS['closure_check']=H(closure)
  def fakeaudit(out,label,expected):
   if mode=='audit-before-failure' and label.endswith('before'):raise ValueError('fake audit before')
   if mode=='audit-after-failure' and label.endswith('after'):raise ValueError('fake audit after')
   return {'fake':True,'label':label}
  mod.run_closure_audit=fakeaudit
  output=case/'out';old=sys.argv;sys.argv=['fake-control','--output',str(output)];failure=None
  with (case/'runner.stdout').open('w') as stdout,contextlib.redirect_stdout(stdout):
   try:mod.main()
   except Exception as exc:failure=repr(exc)
  sys.argv=old;receipt=output/'RESULT.json';steps=json.loads((output/'progress.json').read_text())['steps'] if (output/'progress.json').exists() else []
  if mode in ('success','plane-warning','all-known-warnings'):
   need(failure is None and receipt.is_file() and len(steps)==22,('fake success failed',failure,len(steps)))
   d=json.loads(receipt.read_text());need(d['status']=='PASS_AUTHOR_ONLY_MARKED_SUFFIX' and sum(len(x['axiom_reports']) for x in d['steps'])==58,'fake report inventory')
   need(all(x.get('compiler_command') and x.get('deps_command') and x.get('output_slots') for x in d['steps']),'missing child evidence')
   guard=d['final_direct_and_output_slots'];need(guard[str(output/'lib/Init.olean')] is None and guard[str(output/'lib/Init.olean.private')] is None and guard[str(pkg/'Init.olean')] is not None,'candidate guard missing')
  else:need(failure is not None and not receipt.exists(),('fake accepted injection',mode,failure))
  results[mode]={'accepted':failure is None,'steps_seen':len(steps),'failure':failure}
 print(json.dumps({'status':'PASS_ISOLATED_22_CHILD_FAKE_WRAPPER','runner_sha256':H(RUN),'scope':'synthetic providers, replaced closure-audit callback, fake compiler and fake monitor; no Lean or real parent audit','cases':results},indent=2,sort_keys=True))
