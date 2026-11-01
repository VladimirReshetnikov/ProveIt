from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');PK=R/'Computability/DiophantineConsistency/reviews/pra86-classical-join-snapshot';M=json.loads((PK/'manifest.json').read_text());P=Path('/tmp/pra14-zfc-join-sxrfkso1');B=Path('/tmp/pra14-full-transitive-g3ull6n_');D=Path('/tmp/pra86-classical-preliminary');D.mkdir(exist_ok=True);lib=D/'lib';src=D/'src/DiophantineConsistency';log=D/'logs';lib.mkdir(exist_ok=True);src.mkdir(parents=True,exist_ok=True);log.mkdir(exist_ok=True);sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
s={'status':'RUNNING','phase':'initialization','scope':'Preliminary source-directed 86-operation rebuild on preceding-snapshot classical 14 peer. Parent ancestry not fully reaudited; fixed source snapshot; no current-source or iPRA claim.','records':[]};sp=D/'state.json'
def save():sp.write_text(json.dumps(s,indent=2)+'\n')
save()
try:
 for p in (P/'lib').rglob('*.olean'):
  t=lib/p.relative_to(P/'lib');t.parent.mkdir(parents=True,exist_ok=True)
  if not t.exists():t.symlink_to(p.resolve())
 for n in M['order']:
  f=PK/'frozen'/Path(n.replace('.','/')+'.lean');assert sha(f)==M['source_sha256'][n];shutil.copyfile(f,src/(n.rsplit('.',1)[1]+'.lean'))
 env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(B/'package-lib'),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
 for n in M['order']:
  s.update(phase='compile',module=n);save();f=src/(n.rsplit('.',1)[1]+'.lean');o=lib/(n.replace('.','/')+'.olean');l=log/(n.rsplit('.',1)[1]+'.log');t=time.monotonic()
  with l.open('w') as z:p=subprocess.run([lean,'-M8000','-j1','-DElab.async=false','--root='+str(src.parent),str(f),'-o',str(o)],cwd=R,env=env,stdout=z,stderr=subprocess.STDOUT)
  s['records'].append({'module':n,'exit':p.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l),'seconds':time.monotonic()-t});save();print(n,p.returncode,flush=True)
  if p.returncode:raise RuntimeError(n+'\n'+l.read_text())
 s.update(status='PASS',phase='complete',module=None);save()
except BaseException as e:
 s.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
