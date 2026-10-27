import hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
OUT=Path(Path('/tmp/environment-streams222-controller-latest').read_text().strip())
PIN=json.loads((OUT/'inputs.json').read_text())
NAMES=PIN['fresh_prerequisites']+['ZFCinPA.ValidatorEnvironmentStreams222','ZFCinPA.ValidatorEnvironmentStreams222Checks']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
def recheck():
    require(sha(PIN['compiler'])==PIN['compiler_sha256'],'compiler')
    require(sha(ROOT/'lake-manifest.json')==PIN['manifest_sha256'],'manifest')
    for r in PIN['modules']:
        require(sha(r['source'])==r['source_sha256'],'source '+r['module'])
        for o in r['objects']:require(sha(o['path'])==o['sha256'],'object '+r['module'])
    for r in PIN['external']:require(sha(r['path'])==r['sha256'],'external '+r['module'])
recheck();requested=sys.argv[1:] or NAMES
require(all(n in NAMES for n in requested),'approved leaves only')
stamp=time.time_ns();plan=[]
for n in requested:
    p=ROOT/'Logic/Interpretability/ZFCinPA/Lean'/(n.replace('.','/')+'.lean')
    plan.append({'module':n,'source':str(p),'source_sha256':sha(p)})
(OUT/f'plan-{stamp}.json').write_text(json.dumps(plan,indent=2)+'\n')
env=dict(os.environ,LEAN_PATH=PIN['lean_path'],LEAN_NUM_THREADS='1')
for r in plan:
    require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
    n=r['module'];target=OUT/'lib'/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
    require(not target.is_symlink(),'never overwrite reused artifact')
    log=OUT/'logs'/f'{stamp}-{n.rsplit(".",1)[-1]}.log';timing=log.with_suffix('.time');snapshot=log.with_suffix('.lean')
    snapshot.write_bytes(Path(r['source']).read_bytes())
    if target.exists():
        prior=OUT/'logs'/f'{stamp}-{n.rsplit(".",1)[-1]}.previous.olean'
        shutil.copy2(target,prior);r['preserved_previous_object']={'path':str(prior),'sha256':sha(prior)}
    cmd=[PIN['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(target),r['source']]
    print('START '+n,flush=True);start=time.monotonic()
    with log.open('w') as f:result=subprocess.run(['/usr/bin/time','-v','-o',str(timing)]+cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
    r.update(command=cmd,exit_code=result.returncode,seconds=time.monotonic()-start,
      log=str(log),log_sha256=sha(log),timing=str(timing),timing_sha256=sha(timing),snapshot=str(snapshot),snapshot_sha256=sha(snapshot))
    require(sha(r['source'])==r['source_sha256'],'active source drift')
    if result.returncode==0:r['object']={'path':str(target),'sha256':sha(target),'bytes':target.stat().st_size}
    (OUT/f'run-{stamp}.json').write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps(r),flush=True);print(log.read_text(),flush=True)
    if result.returncode:sys.exit(result.returncode)
recheck();print('PASS: requested leaves and exact source/object postchecks',flush=True)
