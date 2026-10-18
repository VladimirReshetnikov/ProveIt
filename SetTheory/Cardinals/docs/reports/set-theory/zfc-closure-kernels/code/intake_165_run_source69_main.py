from pathlib import Path
import json,os,shutil,signal,subprocess,time
S=Path('/tmp/zfc-intake-165-planning/extracted/zfc-sub246-research-20261018/zfc-sub246-research-20261018')
W=Path('/tmp/zfc-intake-165-source69-main-run1');assert not W.exists();W.mkdir()
P=W/'package';shutil.copytree(S,P)
command=['python3','-B','code/verify_all.py'];start=time.monotonic();timed_out=False
with (W/'stdout.log').open('w') as out,(W/'stderr.log').open('w') as err:
 proc=subprocess.Popen(command,cwd=P,stdout=out,stderr=err,start_new_session=True)
 try:code=proc.wait(timeout=180)
 except subprocess.TimeoutExpired:
  timed_out=True;os.killpg(proc.pid,signal.SIGTERM)
  try:code=proc.wait(timeout=5)
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);code=proc.wait()
record=dict(status='PASS' if code==0 and not timed_out else 'FAIL',scope='Default delivered source69 functional suite, run unchanged on a fresh complete outside-repository copy. Does not replay optional large searches, compile proof sources or verify delivery-checksum manifests.',source=str(S),copy=str(P),command=command,timeout_seconds=180,seconds=time.monotonic()-start,exit_code=code,timed_out=timed_out,stdout=str(W/'stdout.log'),stderr=str(W/'stderr.log'))
summary=P/'results/verification-summary.json'
if code==0:record['summary']=json.loads(summary.read_text())
(W/'execution.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2));raise SystemExit(code if not timed_out else 124)
