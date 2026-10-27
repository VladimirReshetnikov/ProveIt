from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def rec(p):return dict(path=str(p),sha256=sha(p))
mp=V/'thirteen-second-first-norm-corrections-replay.json';assert sha(mp)=='42814c37ce37145da10d71f0450c09d892f6c183ae51ad9179538a7ec7d6abeb';a=json.loads(mp.read_text());i=a['inputs'];p=Path(tempfile.mkdtemp(prefix='second-firstnorm-current-root-'));lib=p/'lib';lib.mkdir();pins=[rec(mp),i['parent_plan'],i['parent_state'],i['root84_receipt'],i['compiler'],*a['source_files'],*i['sources'],*i['companions']]
for e in i['selected_custom']:
 pins.extend([e['source'],e['current_source'],e['object']]);n=e['module'];q=lib/Path(*n.split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(e['object']['path'])
for e in pins:check(e)
assert len(i['selected_custom'])==370
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*i['LEAN_PATH'].split(':')[1:]]);env.pop('LEAN_SRC_PATH',None);s=dict(status='RUNNING',private=str(p),driver_sha256=sha(__file__),cached_project_modules=370,pins=pins,completed=[])
def save():(p/'ROOT.json').write_text(json.dumps(s,indent=2)+'\n')
save();Path('/tmp/second-firstnorm-current-root-location.txt').write_text(str(p))
try:
 for e in a['run']:
  assert shutil.disk_usage(p).free>=512*1024**2;check(e['object']);src=Path(e['path']);assert sha(src)==e['sha256'];n=e['module'];out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.is_symlink();log=p/(n+'.txt');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
  with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x=dict(module=n,source=rec(src),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['completed'].append(x);save();assert code==0,n
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
  for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
  x['matches_author']=x['object']['sha256']==e['object']['sha256'];save();print(json.dumps(x),flush=True)
 for e in pins:check(e)
 s['status']='PASS';save();print(json.dumps(dict(status='PASS',private=str(p),cached=370,reports=sum(len(e['axiom_reports'])for e in s['completed']))),flush=True)
except BaseException as exc:
 s.update(status='FAILED',failure=str(exc));save();raise
