"""Independent saved-packet read with before/after byte binding; no proof compiler."""
from pathlib import Path
import hashlib,json,subprocess,time,sys
S=Path('/tmp/k215-phase11-publication-peer');P=Path('/tmp/k215-phase11-published/lean');H=Path('/tmp/k215-phase11-publication');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(H/'freeze.json')=='6710724209e3bdbba299b44ef01723ea70b8cf30a2c15b85e0f8a33f44f0604c'
f=json.loads((H/'freeze.json').read_text())
for n in ['basis.py','basis-reference.json','packet.py','review_saved.py','README.md']:assert sha(P/n)==f['files'][n]['sha256']
names=['basis.py','basis-reference.json','packet.py','review_saved.py','README.md','execution.tar.gz','index.json','result.json'];before={n:sha(P/n)for n in names}
assert not(S/'saved-review.json').exists()
cmd=[sys.executable,'-B',str(P/'review_saved.py'),'--packet',str(P),'--basis-repo',str(R),'--repo',str(R),'--output',str(S/'saved-review.json')]
t=time.monotonic()
with(S/'saved-reader.stdout.log').open('wb')as out,(S/'saved-reader.stderr.log').open('wb')as err:r=subprocess.run(cmd,stdout=out,stderr=err)
actual={'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,'before':before,'after':{n:sha(P/n)for n in names},'stdout_sha256':sha(S/'saved-reader.stdout.log'),'stderr_sha256':sha(S/'saved-reader.stderr.log'),'wrapper_sha256':sha(__file__),'compiler_invocations':0}
(S/'saved-reader-actual.json').write_text(json.dumps(actual,indent=2)+'\n');assert actual['before']==actual['after'];assert r.returncode==0
result=json.loads((S/'saved-review.json').read_text());assert result['status']=='PASS_SAVED_PHASE11'and result['current_sources_checked']
print(json.dumps({'status':result['status'],'current_sources_checked':result['current_sources_checked'],'archive_members':result['archive_members'],'archive_sha256':result['archive_sha256'],'receipt_sha256':sha(S/'saved-review.json'),'actual_sha256':sha(S/'saved-reader-actual.json'),'seconds':actual['seconds']},indent=2))
