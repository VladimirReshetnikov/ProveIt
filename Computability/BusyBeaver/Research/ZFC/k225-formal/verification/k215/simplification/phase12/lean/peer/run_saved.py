"""Run the reviewed, held saved reader; record outer exit and immutable packet bytes."""
from pathlib import Path
import argparse,hashlib,json,os,signal,subprocess,sys,time
p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,required=True);p.add_argument('--repo',type=Path,required=True);a=p.parse_args()
O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not(O/'saved-reader-actual.json').exists()and not(O/'saved-review.json').exists()
freeze=Path('/tmp/k215-phase12-publication/freeze.json')
assert sha(freeze)=='23d05264e1ac30bdcb6b978526c8b3eb584d7c4d604ff68e432763a2dbfbbf45'
f=json.loads(freeze.read_text())
for name in ['basis.py','basis-reference.json','packet.py','review_saved.py','README.md']:
 assert sha(a.packet/name)==f['files'][name]['sha256']
names=['basis.py','basis-reference.json','packet.py','review_saved.py','README.md','execution.tar.gz','index.json','result.json']
before={n:sha(a.packet/n)for n in names}
cmd=[sys.executable,'-B',str(a.packet/'review_saved.py'),'--packet',str(a.packet),'--basis-repo',str(a.repo),'--repo',str(a.repo),'--output',str(O/'saved-review.json')]
t=time.monotonic();exc=None;exit_code=None
with(O/'saved-reader.stdout.log').open('wb')as stdout,(O/'saved-reader.stderr.log').open('wb')as stderr:
 process=subprocess.Popen(cmd,stdout=stdout,stderr=stderr,start_new_session=True)
 try:exit_code=process.wait(timeout=180)
 except BaseException as e:
  exc=repr(e)
  try:os.killpg(process.pid,signal.SIGKILL)
  except ProcessLookupError:pass
  exit_code=process.wait()
after={n:sha(a.packet/n)for n in names}
r={'status':'PASS'if exit_code==0 and exc is None and before==after else'FAIL','command':cmd,'exit_code':exit_code,'exception':exc,'elapsed_seconds':time.monotonic()-t,'before':before,'after':after,'packet_unchanged':before==after,'reviewed_helper_freeze_sha256':sha(freeze),'wrapper_sha256':sha(__file__),'stdout_sha256':sha(O/'saved-reader.stdout.log'),'stderr_sha256':sha(O/'saved-reader.stderr.log'),'scope':'Independent saved-record/current-source verification only; no Lean, producer, supplied program or archived-code execution; saved recorded object provenance, not fresh live object rehash.'}
if(O/'saved-review.json').exists():r['saved_review_sha256']=sha(O/'saved-review.json')
(O/'saved-reader-actual.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2));assert r['status']=='PASS'
