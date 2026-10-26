from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def rec(p):return dict(path=str(p),sha256=sha(p))
mp=V/'thirteen-first-norm-correction92-replay.json';assert sha(mp)=='a88cecd0f66effc9f17b51702c48a07f746f236cf38b6ba3a055dbd62b0cdd00';a=json.loads(mp.read_text());parent=Path(Path('/tmp/current-narrow-native-root-location.txt').read_text());bp=parent/'plan.json';sp=parent/'state.json';b=json.loads(bp.read_text());bs=json.loads(sp.read_text());assert bs['status']=='PASS';assert sha(bp)==bs['plan_sha256']
mods={e['module']:dict(e)for e in b['modules']}
for e in bs['completed']:mods[e['module']]['object']=e['object']
needed=set()
def visit(n):
 if n in needed:return
 needed.add(n)
 for dep in mods[n]['imports']:
  if dep in mods:visit(dep)
visit('DiophantineConsistency.ThirteenUnitSphere96');p=Path(tempfile.mkdtemp(prefix='firstnorm92-current-root-'));lib=p/'lib';lib.mkdir();pins=[rec(mp),rec(bp),rec(sp),b['compiler'],*a['sources_and_finite_files']]
for n in sorted(needed):
 e=mods[n];pins += [e['source'],e['object']];q=lib/Path(*n.split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(e['object']['path'])
for e in pins:check(e)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*b['external_lean_path']]);env.pop('LEAN_SRC_PATH',None);s=dict(status='RUNNING',private=str(p),driver_sha256=sha(__file__),parent_plan_sha256=sha(bp),parent_state_sha256=sha(sp),cached_project_modules=len(needed),pins=pins,completed=[])
def save():(p/'ROOT.json').write_text(json.dumps(s,indent=2)+'\n')
save();Path('/tmp/firstnorm92-current-root-location.txt').write_text(str(p))
try:
 for e in a['run']:
  assert shutil.disk_usage(p).free>=512*1024*1024;check(e['object']);src=Path(e['path']);assert sha(src)==e['sha256'];n=e['module'];out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);log=p/(n+'.txt');cmd=[b['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
  with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x=dict(module=n,source=rec(src),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['completed'].append(x);save();assert code==0,n
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
  for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
  x['matches_historical_author']=x['object']['sha256']==e['object']['sha256'];save();print(json.dumps(x),flush=True)
 for e in pins:check(e)
 for e in a['sources_and_finite_files']:check(e)
 s['status']='PASS';save();print(json.dumps(dict(status='PASS',private=str(p),cached=len(needed),reports=sum(len(e['axiom_reports'])for e in s['completed']))),flush=True)
except BaseException as exc:
 s.update(status='FAILED',failure=str(exc));save();raise
