"""Own bounded wrapper for explicitly authorized metadata capture/read only."""
from pathlib import Path
import argparse,hashlib,json,subprocess,time,os,signal
p=argparse.ArgumentParser();p.add_argument('kind',choices=['capture','saved']);p.add_argument('--freeze',required=True);p.add_argument('--peer',type=Path,required=True);a=p.parse_args()
S=Path('/tmp/k215-phase15-publication');E=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');out=Path('/tmp/k215-phase15-published/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2)+'\n')
assert sha(S/'freeze.json')==a.freeze;freeze=read(S/'freeze.json')
for n,h in freeze['files'].items():assert sha(S/n)==h
assert a.peer.is_file();recfile=E/(a.kind+'-actual.json');assert not recfile.exists()
argv=['python3','-B',str(S/'collect.py'),'--basis-repo',str(R),'--out',str(out)]if a.kind=='capture'else['python3','-B',str(out/'review_saved.py'),'--basis-repo',str(R),'--repo',str(R),'--output',str(E/'saved-review.json')]
core={p.name:sha(p)for p in out.iterdir()if p.is_file()}if a.kind=='saved'else{}
stdout=E/(a.kind+'.stdout.log');stderr=E/(a.kind+'.stderr.log');start=time.monotonic();timed=False
with stdout.open('wb')as so,stderr.open('wb')as se:
 proc=subprocess.Popen(argv,cwd=R,stdout=so,stderr=se,start_new_session=True)
 try:exit_code=proc.wait(timeout=240)
 except subprocess.TimeoutExpired:
  timed=True;os.killpg(proc.pid,signal.SIGKILL);exit_code=proc.wait()
 except BaseException:
  os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
for n,h in freeze['files'].items():assert sha(S/n)==h
if a.kind=='saved':assert core=={p.name:sha(p)for p in out.iterdir()if p.is_file()}
rec={'status':'PASS_OUTER_EXIT_ZERO'if exit_code==0 else'FAIL_OUTER_EXIT','argv':argv,'cwd':str(R),'exit_code':exit_code,'seconds':time.monotonic()-start,'timeout_seconds':240,'timed_out':timed,'stdout':str(stdout),'stdout_sha256':sha(stdout),'stderr':str(stderr),'stderr_sha256':sha(stderr),'helper_freeze_sha256':a.freeze,'source_peer':str(a.peer),'source_peer_sha256':sha(a.peer),'frozen_files_unchanged':True,'core_before':core,'wrapper_sha256':sha(__file__)}
save(recfile,rec);print(json.dumps(rec,indent=2));raise SystemExit(exit_code)
