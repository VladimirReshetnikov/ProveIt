from pathlib import Path
import json,hashlib,re,os,shutil,subprocess,tempfile,sys,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';MARK=Path('/tmp/command-circuitperm222-root-author-location.txt');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
NAMES=['ArithmeticCommandCircuitPerm222','ArithmeticCommandCircuitPerm222Checks']
if sys.argv[1]=='prepare':
 p0=V/'arithmetic-command-leafperm222-root-replay/ROOT.json';assert sha(p0)=='a50950f0b704ea6bf9d08991b6feb0bee63b5d014526d055d799c7383922c9cd';root=json.loads(p0.read_text());a=json.loads(Path(root['author_record']['path']).read_text());check(a['inputs']);base=json.loads(Path(a['inputs']['path']).read_text());r=root['records'][0];assert root['status']=='PASS' and r['matches_author'];mods=[*base['modules'],dict(module=r['module'],source=r['source']['path'],source_sha256=r['source']['sha256'],imports=['Init','DiophantineConsistency.ArithmeticCommandBlockPerm222'],objects=[r['object']])];assert len(mods)==124 and sum(len(m['objects'])for m in mods)==409
 pins=[rec(p0),root['author_record'],a['inputs'],rec(__file__),base['compiler'],*root['pins'],rec(R/'lean-toolchain'),rec(R/'lake-manifest.json')]
 for m in mods:
  assert sha(m['source'])==m['source_sha256'];actual=list(dict.fromkeys(['Init']+[n for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(m['source']).read_text(),re.M)for n in line.split('--',1)[0].split()]));assert actual==list(dict.fromkeys(m['imports'])),m['module'];pins.append(dict(path=m['source'],sha256=m['source_sha256']));pins.extend(m['objects'])
 for e in pins:check(e)
 p=Path(tempfile.mkdtemp(prefix='command-circuitperm222-root-author-'));lib=p/'lib';lib.mkdir();assert shutil.disk_usage(p).free>=512*1024**2
 for m in mods:
  for o in m['objects']:
   q=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
 i=dict(modules=mods,pins=pins,compiler=base['compiler'],lean_path=':'.join([str(lib),*base['lean_path'].split(':')[1:]]),counts=dict(custom=124,Foundation=95,artifacts=409,external=38));save(p/'inputs.json',i);MARK.write_text(str(p));print(json.dumps(dict(status='PREPARED',private=str(p),pins=len(pins))))
else:
 p=Path(MARK.read_text());i=json.loads((p/'inputs.json').read_text());d=p/('attempt-'+str(time.time_ns()));d.mkdir();s=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[]);save(d/'RESULT.json',s);env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for e in i['pins']:check(e)
 for n in NAMES:
  assert shutil.disk_usage(p).free>=512*1024**2;src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(n+'.lean');snap=d/(n+'.lean');shutil.copyfile(src,snap);out=p/'lib/DiophantineConsistency'/(n+'.olean');assert not out.is_symlink()
  if out.exists():shutil.copyfile(out,d/(n+'.previous.olean'))
  log=d/(n+'.log');timing=d/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];t=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  r=dict(module='DiophantineConsistency.'+n,source=rec(src),snapshot=rec(snap),command=cmd,seconds=time.monotonic()-t,exit_code=code,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);s['records'].append(r);save(d/'RESULT.json',s);print(json.dumps(r),flush=True);assert sha(src)==sha(snap)
  if code:s['status']='FAILED';save(d/'RESULT.json',s);print(log.read_text(),flush=True);raise SystemExit(code)
  r['axiom_reports']=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
  for title,ax in r['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 for e in i['pins']:check(e)
 s['status']='PASS';save(d/'RESULT.json',s);save(p/'LATEST.json',rec(d/'RESULT.json'));print(json.dumps(dict(status='PASS',private=str(p),result=str(d/'RESULT.json'))),flush=True)
