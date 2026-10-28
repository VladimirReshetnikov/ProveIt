from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
ap=V/'arithmetic-command-wordperm222-replay.json';a=json.loads(ap.read_text());i=a['inputs'];mods=list(i['modules']);main=a['final_records'][0];mods.append(dict(module=main['module'],source=main['source']['path'],source_sha256=main['source']['sha256'],objects=[main['object']]));p=Path(tempfile.mkdtemp(prefix='fetch222-root-author-'));lib=p/'lib';lib.mkdir();pins=[*i['pins'],rec(ap),main['source'],main['object'],rec(__file__)]
for e in mods:
 assert sha(e['source'])==e['source_sha256']
 for o in e['objects']:
  check(o);q=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
for e in pins:check(e)
inputs=dict(modules=mods,pins=pins,compiler=i['compiler'],compiler_sha256=i['compiler_sha256'],manifest_sha256=i['manifest_sha256'],external=i['external'],lean_path=':'.join([str(lib),*i['lean_path'].split(':')[1:]]),scope='102 cached modules,86 Foundation,37 boundaries; no prerequisite build');save(p/'inputs.json',inputs);Path('/tmp/fetch222-root-author-location.txt').write_text(str(p));env=os.environ.copy();env['LEAN_PATH']=inputs['lean_path'];env.pop('LEAN_SRC_PATH',None);s=dict(status='RUNNING',inputs_sha256=sha(p/'inputs.json'),driver_sha256=sha(__file__),records=[]);save(p/'run.json',s)
for name in ['ArithmeticCommandFetchPerm222','ArithmeticCommandFetchPerm222Checks']:
 assert shutil.disk_usage(p).free>=512*1024**2;src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(name+'.lean');out=lib/'DiophantineConsistency'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.is_symlink();snapshot=p/(name+'.lean');shutil.copyfile(src,snapshot);log=p/(name+'.log');cmd=[i['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x=dict(module='DiophantineConsistency.'+name,source=rec(src),snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['records'].append(x);save(p/'run.json',s);print(json.dumps(x),flush=True)
 if code:s['status']='FAILED';save(p/'run.json',s);raise SystemExit(code)
 reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
for e in pins:check(e)
for e in s['records']:check(e['source'])
s['status']='PASS';save(p/'run.json',s);print('PASS '+str(p),flush=True)
