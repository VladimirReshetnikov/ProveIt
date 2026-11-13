#!/usr/bin/env python3
"""Exercise actual six-child wrapper with synthetic providers and fake compiler."""
import contextlib,hashlib,importlib.util,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
HERE=Path(__file__).resolve().parent;RUN=HERE/'replay.py';REAL=Path('/home/codex/.codex/worktrees/46be/Proofs');PLAN=REAL/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-halt-compact-audited-plan'; HISTORY=REAL/'Computability/DiophantineConsistency/reviews/ha87-isolated-full-author-pass/logs';SAVED=json.loads((PLAN/'source-scan.json').read_text());H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
FAKE=r'''#!/usr/bin/python3
import os,re,sys,json
from pathlib import Path
case=Path(CASE);mode=(case/'mode').read_text();lib,pkg=map(Path,os.environ['LEAN_PATH'].split(':'));args=sys.argv[1:]
if '--deps' in args:
 src=Path(args[-1]);deps=['Init']+re.findall(r'^import\s+([\w.]+)',src.read_text(),re.M)
 for dep in deps:
  rel=Path(*dep.split('.')).with_suffix('.olean');live=[x for x in (lib/rel,pkg/rel) if x.is_file()]
  if not live:sys.exit(12)
  print(live[0])
 if mode=='wrong-deps':print(case/'bad.olean')
 sys.exit(0)
src=Path(next(x for x in args if x.endswith('.lean')));obj=Path(args[args.index('-o')+1]);counter=case/'count';n=int(counter.read_text())+1 if counter.exists() else 1;counter.write_text(str(n));obj.parent.mkdir(parents=True,exist_ok=True)
if mode=='nonzero' and n==2:sys.exit(8)
if mode=='shadow-object' and n==1:(lib/'Init.olean').write_bytes(b'shadow')
if mode=='shadow-companion' and n==1:(lib/'Init.olean.private').write_bytes(b'shadow')
if mode=='package-companion' and n==1:(pkg/'Init.olean.private').write_bytes(b'extra')
if mode=='previous-output-mutate' and n==2:(lib/'DiophantineConsistency/ArithmeticRunTrace.olean').write_bytes(b'changed')
if mode=='late-source-mutate' and n==6:(src.parent/'ArithmeticRunTrace.lean').write_text('changed')
if mode=='source-symlink' and n==2:
 p=src.parent/'ArithmeticRunTrace.lean';t=case/'same-source';t.write_bytes(p.read_bytes());p.unlink();p.symlink_to(t)
if mode=='redirect-directory' and n==1:
 old=obj.parent;old.rename(case/'saved-project');(case/'outside').mkdir();old.symlink_to(case/'outside',target_is_directory=True)
if mode=='symlink-output' and n==1:
 t=case/'external-output';t.write_bytes(b'object');obj.symlink_to(t)
elif mode!='missing-output' or n!=1:obj.write_bytes(('fake-object-'+str(n)).encode())
if mode=='output-companion' and n==1:Path(str(obj)+'.private').write_bytes(b'extra')
if n<=5:
 baselines=json.loads((case/'baselines.json').read_text());text=baselines[src.stem].replace('<SOURCE>',str(src))
 if mode=='warning-modified' and n==1:text=text.replace('warning:','warning: modified',1)
 if mode=='warning-missing' and n==1:text=''
 if mode=='warning-extra' and n==1:text+='warning: injected\n'
 if mode=='warning-wrong-path' and n==1:text=text.replace(str(src),'/tmp/wrong.lean',1)
 if mode=='sorry' and n==1:text+='sorryAx'
 print(text,end='')
else:
 name='CompactHaltWord.halt_compact_word' if mode!='wrong-report' else 'Wrong.report'
 ax='propext, Classical.choice, Quot.sound' if mode!='extra-axiom' else 'propext, Wrong.axiom'
 if mode!='missing-report':print("'"+name+"' depends on axioms: ["+ax+"]")
'''
MON='''import os,subprocess\nfrom pathlib import Path\ndef overlay(base,dest):\n for root,dirs,files in os.walk(base,followlinks=False):\n  root=Path(root);out=dest/root.relative_to(base);out.mkdir(parents=True,exist_ok=True)\n  for name in files:(out/name).symlink_to(root/name)\ndef monitored(cmd,env,log,timeout=600):\n with log.open('x') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)\n return r.returncode,123456,None\n'''
modes=['success','nonzero','shadow-object','shadow-companion','package-companion','previous-output-mutate','late-source-mutate','source-symlink','redirect-directory','symlink-output','missing-output','output-companion','warning-modified','warning-missing','warning-extra','warning-wrong-path','sorry','wrong-deps','wrong-report','extra-axiom','missing-report','audit-before-failure','audit-after-failure','closure-schema-boolean','parent-schema-invalid','scan-mismatch','audit-after-source-mutation','audit-after-shadow','audit-after-output-mutation']
with tempfile.TemporaryDirectory(prefix='halt-word-fake-',dir='/tmp') as temp:
 root=Path(temp);results={}
 for j,mode in enumerate(modes):
  case=root/mode;case.mkdir();repo=case/'repo';repo.mkdir();plan=case/'plan';plan.mkdir();parent=case/'parent';parent.mkdir();closure=case/'closure';closure.mkdir();seed=case/'seed';seed.mkdir();pkg=case/'package';pkg.mkdir();(pkg/'Init.olean').write_bytes(b'init');(case/'mode').write_text(mode)
  spec=importlib.util.spec_from_file_location('draft_'+mode.replace('-','_'),RUN);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
  rows=[]
  for row in SAVED['sources']:
   dest=repo/row['source'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((REAL/row['source']).read_bytes());rows.append(dict(row))
  for fn in ('diagnostic_policy.py','scan.py'):(plan/fn).write_bytes((PLAN/fn).read_bytes())
  names={x['module'] for x in rows};direct={'Init'}
  for row in rows:direct.update(x for x in row['imports'] if x not in names)
  for dep in direct-{'Init'}:
   obj=(seed/Path(*dep.split('.'))).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(('seed-'+dep).encode())
  util=m.load(m.UTIL,'util_'+str(j));cand={}
  for dep in direct:
   cand[dep]=[{'root':str(r),'slots':util.slots(r/Path(*dep.split('.')))} for r in (seed,pkg)]
  baselines={};histroot='/tmp/ha87-frozen-full-e_jgyudl/tree/Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
  for short,x in SAVED['diagnostic_baselines'].items():
   src=HISTORY/f'DiophantineConsistency_{short}-attempt-1.log';dst=repo/x['historical_log'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());baselines[short]=src.read_text().replace(histroot+short+'.lean','<SOURCE>')
  (case/'baselines.json').write_text(json.dumps(baselines));scan={'status':'PASS_POINT_IN_TIME_AUDITED_SUFFIX_HALT_SOURCE_SCAN','sources':rows,'direct_candidates':cand,'target_slots':{r['module']:[] for r in rows},'diagnostic_baselines':SAVED['diagnostic_baselines']};(plan/'source-scan.json').write_text(json.dumps(scan));scan_sha=H(plan/'source-scan.json')
  pcheck={'status':'PASS_INDEPENDENT_AUTHOR_ONLY_FINAL_SUFFIX_ARTIFACT_AUDIT','result_sha256':'fake-result','source_modules':22,'lean_launched':False};(parent/'CHECK.json').write_text(json.dumps(pcheck));(parent/'audit.py').write_text('fake');ccheck={'status':'PASS_NO_LEAN_AUDITED_SUFFIX_HALT_SOURCE_REVIEW','reviewed_commit':'5b35381d4b','scan_sha256':scan_sha,'source_count':6,'direct_modules':5,'direct_candidate_slots':100,'target_slots':120,'diagnostic_baselines':5,'diagnostic_controls':55,'parent_audit_rerun_exit':0,'parent_check_sha256':H(parent/'CHECK.json'),'scan_rerun_exit':0,'optimized_controls_exit':1,'lean_launched':False};
  if mode=='closure-schema-boolean':ccheck['parent_audit_rerun_exit']=True
  if mode=='parent-schema-invalid':pcheck['lean_launched']=True;(parent/'CHECK.json').write_text(json.dumps(pcheck));ccheck['parent_check_sha256']=H(parent/'CHECK.json')
  (closure/'CHECK.json').write_text(json.dumps(ccheck));(closure/'terminal-observation.json').write_text(json.dumps({'independent_audit_exit':0,'lean_launched':False}));(closure/'audit.py').write_text('fake')
  fakelean=case/'lean';fakelean.write_text(FAKE.replace('CASE',repr(str(case))));fakelean.chmod(0o755);mon=case/'monitor.py';mon.write_text(MON);output=Path('/tmp')/('halt-fake-output-'+str(os.getpid())+'-'+str(j));m.ROOT=repo;m.PLAN=plan;m.PARENT=parent;m.CLOSURE=closure;m.SEED=seed;m.PKG=pkg;m.LEAN=fakelean;m.MON=mon;m.PINS['source-scan.json']=scan_sha;m.FIXED={parent/'CHECK.json':H(parent/'CHECK.json'),seed.parent/'RESULT.json':'fake-result'};m.validate_fixed=lambda:None
  realrun=subprocess.run
  def fake_run(args,**kw):
   if len(args)>=5 and str(args[-1])==str(plan/'scan.py'):return subprocess.CompletedProcess(args,0,b'injected' if mode=='scan-mismatch' else (plan/'source-scan.json').read_bytes(),b'')
   return realrun(args,**kw)
  m.subprocess.run=fake_run
  calls=[0]
  def fake_audit(script,expected):
   calls[0]+=1
   if (mode=='audit-before-failure' and calls[0]==1) or (mode=='audit-after-failure' and calls[0]==3):raise ValueError('injected audit failure')
   if calls[0]==4 and mode=='audit-after-source-mutation':(output/'frozen/DiophantineConsistency/ArithmeticRunTrace.lean').write_text('changed')
   if calls[0]==4 and mode=='audit-after-shadow':(output/'lib/Init.olean.private').write_bytes(b'shadow')
   if calls[0]==4 and mode=='audit-after-output-mutation':(output/'lib/DiophantineConsistency/ArithmeticRunTrace.olean').write_bytes(b'changed')
   return {'exit':0,'stdout_sha256':'synthetic'}
  m.run_audit=fake_audit
  old=sys.argv;sys.argv=[str(RUN),'--output',str(output)];err=None
  try:
   with open(os.devnull,'w') as f,contextlib.redirect_stdout(f):m.main()
  except Exception as e:err=repr(e)
  finally:sys.argv=old;m.subprocess.run=realrun
  if output.exists():shutil.rmtree(output)
  want=(mode=='success')
  if (err is None)!=want:raise RuntimeError((mode,'unexpected result',err))
  results[mode]={'passed':err is None,'expected_pass':want,'rejection':err}
 print(json.dumps({'status':'PASS_SYNTHETIC_HALT_WRAPPER_CONTROLS','cases':len(results),'results':results,'limitations':'synthetic providers, fake compiler and monitor, replaced audit and fixed-pin callbacks; not a Lean or real audit run'},indent=2,sort_keys=True))
