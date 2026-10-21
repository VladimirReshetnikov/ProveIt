"""Invoke the reviewed local saved reader and retain exact process evidence."""
from pathlib import Path
import hashlib,json,subprocess,sys,time

PACKET=Path('/tmp/k215-phase10-published/lean')
OUT=Path('/tmp/k215-phase10-publication-peer')
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
FILES=['basis.py','basis-reference.json','packet.py','review_saved.py','README.md','execution.tar.gz','index.json','result.json']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
before={n:sha(PACKET/n)for n in FILES}
assert before['packet.py']=='132e9bc9917b29b01d07824345e813d2889bf951d648cc27ca215461bb10ff5d'
assert before['review_saved.py']=='c708afce9999664d7fe627646ff5022d363435f2866bf03e5c4cc600bec202f4'
assert before['basis.py']=='a9a20928a580187bb1c188523d17af6f96f882f201650be0b4735ec79fda6c22'
result_path=OUT/'saved-review.json'
assert not result_path.exists()
argv=[sys.executable,'-B',str(PACKET/'review_saved.py'),'--packet',str(PACKET),'--basis-repo',str(REPO),'--repo',str(REPO),'--output',str(result_path)]
start=time.monotonic()
with (OUT/'saved.stdout').open('xb')as stdout,(OUT/'saved.stderr').open('xb')as stderr:
    result=subprocess.run(argv,cwd=REPO,stdout=stdout,stderr=stderr,timeout=120)
elapsed=time.monotonic()-start
after={n:sha(PACKET/n)for n in FILES}
record={'argv':argv,'cwd':str(REPO),'exit_code':result.returncode,'elapsed_seconds':elapsed,'timeout_seconds':120,'packet_before':before,'packet_after':after,'packet_unchanged':before==after,'stdout_sha256':sha(OUT/'saved.stdout'),'stderr_sha256':sha(OUT/'saved.stderr'),'reader_result_sha256':sha(result_path)if result_path.exists()else None,'compiler_invoked':False,'producer_invoked':False}
(OUT/'saved-reader-actual.json').write_text(json.dumps(record,indent=2)+'\n')
assert result.returncode==0 and before==after
checked=json.loads(result_path.read_text())
assert checked['status']=='PASS_SAVED_PHASE10'and checked['current_sources_checked']
assert checked['modules']==197 and checked['fresh_count']==8 and checked['phase9_reused_count']==189
assert checked['isolated_warning_occurrences']==6 and checked['isolated_fresh_warnings']==0
print(json.dumps({'status':checked['status'],'exit_code':result.returncode,'elapsed_seconds':elapsed,'receipt_sha256':sha(OUT/'saved-reader-actual.json'),'saved_review_sha256':sha(result_path)}))
