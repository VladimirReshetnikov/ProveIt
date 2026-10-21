from pathlib import Path
import fcntl,hashlib,json,os,signal,subprocess,time
H=Path(__file__).resolve().parent;W=H/'api-check';W.mkdir()
src=W/'Audit.lean';src.write_bytes((H/'Audit.lean').read_bytes())
cache=H/'run001/cache';lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={str(p):sha(p) for p in [src,lean,*cache.rglob('*.olean')]}
argv=[str(lean),'-j1','-M4096','--root='+str(W),'-o',str(W/'Audit.olean'),str(src)]
env=os.environ.copy();env['LEAN_PATH']=str(cache);env['LEAN_NUM_THREADS']='1'
def stop(sig,frame):raise KeyboardInterrupt(f'signal {sig}')
signal.signal(signal.SIGTERM,stop)
with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX);start=time.monotonic()
 with (W/'compiler.log').open('wb') as f:
  proc=subprocess.Popen(argv,stdout=f,stderr=subprocess.STDOUT,env=env,cwd=W,start_new_session=True)
  try:code=proc.wait(timeout=60)
  except BaseException:
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
 elapsed=time.monotonic()-start
r={'status':'PASS' if code==0 else 'FAIL','argv':argv,'exit_code':code,'seconds':elapsed,'source_sha256':sha(src),'log_sha256':sha(W/'compiler.log'),'inputs':pins,'inputs_unchanged':all(sha(p)==s for p,s in pins.items())}
(W/'actual.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='inputs'}))
