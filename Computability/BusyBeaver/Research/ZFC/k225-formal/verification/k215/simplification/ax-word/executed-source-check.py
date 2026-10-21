from pathlib import Path
import argparse,fcntl,hashlib,json,os,signal,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);args=p.parse_args()
H=Path(__file__).resolve().parent; W=args.output.resolve(); W.mkdir()
C=Path('/tmp/k215-lean-complete/workspace/.lake/build/lib/lean')
cache=W/'cache';cache.mkdir(); source=W/'BusyBeaver/ZFC/L2AxiomsPerm.lean';source.parent.mkdir(parents=True)
source.write_bytes((H/'L2AxiomsPerm.lean').read_bytes())
for f in C.rglob('*.olean'):
 t=cache/f.relative_to(C);t.parent.mkdir(parents=True,exist_ok=True);t.symlink_to(f)
obj=cache/'BusyBeaver/ZFC/L2AxiomsPerm.olean';obj.unlink()
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={str(f):sha(f) for f in [source,lean,*C.rglob('*.olean')]}
env=os.environ.copy();env['LEAN_PATH']=str(cache);env['LEAN_NUM_THREADS']='1'
argv=[str(lean),'-j1','-M4096','--root='+str(W),'-o',str(obj),str(source)]
log=W/'compiler.log';timeout=False
record={'argv':argv,'source_sha256':sha(source),'status':'WAITING_FOR_LOCK','inputs':pins}
(W/'actual.json').write_text(json.dumps(record,indent=2)+'\n')
def stop(sig,frame):raise KeyboardInterrupt(f'signal {sig}')
signal.signal(signal.SIGTERM,stop)
with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX);start=time.monotonic();record['status']='RUNNING';(W/'actual.json').write_text(json.dumps(record,indent=2)+'\n')
 with log.open('wb') as f:
  proc=subprocess.Popen(argv,stdout=f,stderr=subprocess.STDOUT,env=env,cwd=W,start_new_session=True)
  try:code=proc.wait(timeout=120)
  except BaseException as ex:
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=proc.returncode;timeout=isinstance(ex,subprocess.TimeoutExpired)
   if not timeout:raise
 elapsed=time.monotonic()-start
record.update(status='PASS' if code==0 else 'FAIL',exit_code=code,timed_out=timeout,seconds=elapsed,log_sha256=sha(log),object_sha256=sha(obj) if obj.exists() else None,inputs_unchanged=all(sha(f)==h for f,h in pins.items()))
(W/'actual.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items() if k!='inputs'}),flush=True)
