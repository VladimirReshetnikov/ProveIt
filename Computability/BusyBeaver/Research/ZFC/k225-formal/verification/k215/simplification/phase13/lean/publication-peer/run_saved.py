from pathlib import Path
import argparse,datetime,hashlib,json,os,signal,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('--packet',required=True,type=Path);args=ap.parse_args()
O=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=args.packet.resolve();F=Path('/tmp/k215-phase13-publication/freeze.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(F)=='d7ae992e234a3d35656998ea6f724c64e59a3c6a0ff47ae326686c76f784c649'
f=json.loads(F.read_text());names=['basis.py','basis-reference.json','packet.py','review_saved.py','README.md','result.json','index.json','execution.tar.gz']
for n in names[:5]:assert sha(P/n)==f['files'][n]
before={n:{'sha256':sha(P/n),'bytes':(P/n).stat().st_size}for n in names}
for n in ['saved-review.json','saved-reader-actual.json','saved-reader.stdout.txt','saved-reader.stderr.txt']:assert not (O/n).exists(),n
cmd=['python3','-B',str(P/'review_saved.py'),'--packet',str(P),'--basis-repo',str(R),'--repo',str(R),'--output',str(O/'saved-review.json')]
start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat();timed_out=False
with (O/'saved-reader.stdout.txt').open('wb')as out,(O/'saved-reader.stderr.txt').open('wb')as err:
 p=subprocess.Popen(cmd,cwd=R,stdout=out,stderr=err,start_new_session=True)
 try:rc=p.wait(timeout=180)
 except subprocess.TimeoutExpired:
  timed_out=True;os.killpg(p.pid,signal.SIGKILL);rc=p.wait()
after={n:{'sha256':sha(P/n),'bytes':(P/n).stat().st_size}for n in names}
v={'status':'PASS_SAVED_READER'if rc==0 and not timed_out and before==after else'FAIL','command':cmd,'started_utc':started,'seconds':time.monotonic()-start,'exit_code':rc,'timed_out':timed_out,'packet_files_before':before,'packet_files_after':after,'packet_bytes_unchanged':before==after,'stdout_sha256':sha(O/'saved-reader.stdout.txt'),'stderr_sha256':sha(O/'saved-reader.stderr.txt'),'wrapper_sha256':sha(__file__),'source_peer_sha256':sha(O/'review-v2.json'),'freeze_sha256':sha(F),'scope':'Independent execution of reviewed saved reader against current repository; no compiler, producer, collector or archived code execution. This checks saved evidence and current sources, not current live compiler objects.'}
if (O/'saved-review.json').is_file():v['saved_review_sha256']=sha(O/'saved-review.json')
(O/'saved-reader-actual.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({k:v[k]for k in ['status','exit_code','seconds','packet_bytes_unchanged']}));raise SystemExit(0 if v['status']=='PASS_SAVED_READER'else 1)
