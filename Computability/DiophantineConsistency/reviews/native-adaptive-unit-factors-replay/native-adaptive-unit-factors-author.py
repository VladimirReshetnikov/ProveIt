from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';A=R/'Computability/DiophantineConsistency/research/adaptive-carrier-bootstrap2011-cache-audit.json';MARK=Path('/tmp/native-adaptive-unit-factors-author-location.txt')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
names=['NativeAdaptiveUnitFactors','NativeAdaptiveUnitFactorsChecks']
if sys.argv[1]=='prepare':
 assert sha(A)=='21917ee6855045afd5c9494868c431f2bd8e2ed67b3ef621e8772f42cdc6b915';a=json.loads(A.read_text());check(a['provider']);s=a['scopes'][0];old=json.loads(Path(a['provider']['path']).read_text());assert len(s['custom'])==25 and len(s['external_boundary'])==22 and not s['unknown_imports']
 pins=[rec(A),a['provider'],old['compiler'],rec(__file__),rec(R/'lean-toolchain'),rec(R/'lake-manifest.json'),*old['pins']]
 modules=[]
 for e in s['custom']:
  check(e['source']);check(e['object']);actual=['Init']+re.findall(r'^import\s+(\S+)',Path(e['source']['path']).read_text(),re.M);assert actual==e['actual_imports'],e['module'];modules.append(dict(module=e['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],objects=[e['object']],imports=actual));pins.extend([e['source'],e['object']])
 for e in s['external_boundary']:pins.extend([e['source'],*e['artifacts']])
 for e in pins:check(e)
 assert shutil.disk_usage('/tmp').free>=512*1024**2
 p=Path(tempfile.mkdtemp(prefix='native-adaptive-unit-factors-root-author-'));lib=p/'lib';lib.mkdir()
 for e in modules:
  for o in e['objects']:
   dest=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(o['path'])
 i=dict(modules=modules,pins=pins,compiler=old['compiler'],lean_path=':'.join([str(lib),*old['LEAN_PATH'][1:]]),counts=dict(custom=25,Foundation=0,artifacts=25,boundaries=22,external_companions=66),snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip());save(p/'inputs.json',i);MARK.write_text(str(p));print(json.dumps(dict(status='PREPARED',private=str(p),pins=len(pins),free=shutil.disk_usage('/tmp').free)))
else:
 p=Path(MARK.read_text());i=json.loads((p/'inputs.json').read_text());lib=p/'lib';attempt=p/('attempt-'+str(time.time_ns()));attempt.mkdir();env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);s=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[]);save(attempt/'RESULT.json',s)
 for e in i['pins']:check(e)
 for name in names:
  assert shutil.disk_usage('/tmp').free>=512*1024**2
  n='DiophantineConsistency.'+name;source=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(name+'.lean');snapshot=attempt/(name+'.lean');shutil.copyfile(source,snapshot);out=lib/'DiophantineConsistency'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.is_symlink()
  if out.exists():shutil.copyfile(out,attempt/(name+'.previous.olean'))
  log=attempt/(name+'.log');timing=attempt/(name+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)];start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x=dict(module=n,source=rec(source),snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);s['records'].append(x);save(attempt/'RESULT.json',s);print(json.dumps(x),flush=True)
  assert sha(source)==sha(snapshot)
  if code:s['status']='FAILED';save(attempt/'RESULT.json',s);print(log.read_text(),flush=True);raise SystemExit(code)
  x['axiom_reports']=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
  for title,ax in x['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
 for e in i['pins']:check(e)
 s['status']='PASS';save(attempt/'RESULT.json',s);save(p/'LATEST.json',rec(attempt/'RESULT.json'));print(json.dumps(dict(status='PASS',private=str(p),result=str(attempt/'RESULT.json'))),flush=True)
