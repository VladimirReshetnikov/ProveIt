from pathlib import Path
import os,json,hashlib,subprocess,signal,time,fcntl,sys,re
signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt('SIGTERM')))
base=Path('/tmp/k215-offset-symmetry');src=Path(sys.argv[1]);out=base/sys.argv[2];out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
repo=Path('/home/codex/.codex/worktrees/ec20/Proofs')
compiler=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
cache=Path('/tmp/k215-proof-simplification/root/objects')
cmd=[str(compiler),'-j1','-M12288','--root='+str(base),'-o',str(out/(src.stem+'.olean')),str(src)]
env=os.environ.copy();env['LEAN_PATH']=str(base/'run2')+':'+str(cache);env['LEAN_NUM_THREADS']='1'
inputs={str(src):sha(src),str(compiler):sha(compiler)}
rows={r['module']:r for r in json.loads((repo/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/lean/result.json').read_text())['module_evidence']}
seen=set()
def bind(m):
 if m in seen:return
 seen.add(m)
 for d in rows[m]['imports']:
  if d in rows:bind(d)
 p=cache/(m.replace('.','/')+'.olean');inputs[str(p)]=sha(p)
for line in re.findall(r'^import ([^\n]+)',src.read_text(),re.M):
 for m in line.split():
  if m=='OffsetSymmetry':inputs[str(base/'run2/OffsetSymmetry.olean')]=sha(base/'run2/OffsetSymmetry.olean')
  else:bind(m)
inputs[str(Path(__file__))]=sha(Path(__file__))
(out/src.name).write_bytes(src.read_bytes())
rec={'command':cmd,'inputs':inputs,'timeout_seconds':120}
print('WAIT_SHARED_LOCK',flush=True)
with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX);start=time.monotonic();print('START',flush=True)
 with (out/'compiler.log').open('w') as log:
  proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,env=env,start_new_session=True)
  try:code=proc.wait(timeout=120)
  except BaseException:
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
 rec.update(exit_code=code,seconds=time.monotonic()-start,log_sha256=sha(out/'compiler.log'),inputs_unchanged=all(sha(p)==h for p,h in inputs.items()))
 rec['status']='PASS' if code==0 and rec['inputs_unchanged'] else 'FAIL'
 if code==0:rec['object_sha256']=sha(out/(src.stem+'.olean'))
 (out/'record.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:v for k,v in rec.items() if k!='inputs'},indent=2));print((out/'compiler.log').read_text())
