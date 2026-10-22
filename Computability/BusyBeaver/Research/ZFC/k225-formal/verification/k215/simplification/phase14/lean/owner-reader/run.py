"""Own authorized metadata execution wrapper; never invokes a proof compiler."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,signal,subprocess,time
S=Path('/tmp/k215-phase14-publication');E=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=json.loads((S/'freeze.json').read_text());assert sha(S/'freeze.json')=='6e7d75b8430ebd2ad0f08bb40fc73761f380988220eb081a84fa420bc5f3b76c'
assert sha('/tmp/k215-phase14-publication-peer/review.json')=='6a6e38fb999d35bbbffa6ce4a52cb18da5f5493028b62bf433efeaca540420d1'
p=argparse.ArgumentParser();p.add_argument('mode',choices=['collect','saved']);a=p.parse_args()
packet=Path('/tmp/k215-phase14-published/lean')
argv=['python3','-B',str(S/'collect.py'),'--basis-repo',str(R),'--out',str(packet)] if a.mode=='collect' else ['python3','-B',str(packet/'review_saved.py'),'--packet',str(packet),'--basis-repo',str(R),'--repo',str(R),'--output',str(E/'saved-review.json')]
paths=[S/n for n in freeze['files']]+[S/'freeze.json']
if a.mode=='saved':paths+=sorted(packet.iterdir())
before={str(p):sha(p) for p in paths};out=E/(a.mode+'.stdout.txt');err=E/(a.mode+'.stderr.txt');record=E/(a.mode+'-actual.json')
assert all(not p.exists() for p in [out,err,record])
rec={'status':'RUNNING','argv':argv,'cwd':str(R),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wrapper_sha256':sha(__file__),'before':before,'stdout':str(out),'stderr':str(err)};record.write_text(json.dumps(rec,indent=2)+'\n')
start=time.monotonic();proc=None
try:
 with out.open('wb') as stdout,err.open('wb') as stderr:
  proc=subprocess.Popen(argv,cwd=R,stdout=stdout,stderr=stderr,start_new_session=True);rec['pid']=proc.pid;record.write_text(json.dumps(rec,indent=2)+'\n');code=proc.wait()
 rec.update(status='PASS_OUTER_EXIT_ZERO' if code==0 else 'FAIL_OUTER_EXIT',exit_code=code)
except BaseException as exc:
 if proc is not None and proc.poll() is None:
  os.killpg(proc.pid,signal.SIGTERM)
  try:proc.wait(timeout=10)
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
 rec.update(status='OUTER_EXCEPTION',exception=repr(exc),exit_code=None if proc is None else proc.returncode);raise
finally:
 after={str(p):sha(p) for p in paths};rec.update(seconds=time.monotonic()-start,after=after,inputs_unchanged=before==after,stdout_sha256=sha(out),stderr_sha256=sha(err));record.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:v for k,v in rec.items() if k not in ['before','after']},indent=2),flush=True)
assert rec['exit_code']==0 and rec['inputs_unchanged']
