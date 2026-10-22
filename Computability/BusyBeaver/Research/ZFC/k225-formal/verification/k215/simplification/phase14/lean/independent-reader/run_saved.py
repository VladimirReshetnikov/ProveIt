"""Invoke only the reviewed saved metadata reader; preserve exit/logs and packet pins."""
from pathlib import Path
import json,hashlib,subprocess,time
S=Path(__file__).resolve().parent;P=Path('/tmp/k215-phase14-published/lean');R=Path('/home/codex/.codex/worktrees/ec20/Proofs');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=['basis.py','basis-reference.json','packet.py','review_saved.py','README.md','execution.tar.gz','index.json','result.json'];before={n:sha(P/n)for n in files};f=json.loads(Path('/tmp/k215-phase14-publication/freeze.json').read_text())
for n in files[:5]:assert before[n]==f['files'][n]
assert not(S/'saved-review.json').exists();argv=['python3','-B',str(P/'review_saved.py'),'--basis-repo',str(R),'--repo',str(R),'--output',str(S/'saved-review.json')];t=time.monotonic();r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
(S/'saved.stdout.txt').write_bytes(r.stdout);(S/'saved.stderr.txt').write_bytes(r.stderr);after={n:sha(P/n)for n in files}
a={'status':'PASS_SAVED_READER_OUTER'if r.returncode==0 and before==after else'FAIL','argv':argv,'exit_code':r.returncode,'seconds':time.monotonic()-t,'before':before,'after':after,'stdout_sha256':sha(S/'saved.stdout.txt'),'stderr_sha256':sha(S/'saved.stderr.txt'),'review_sha256':sha(S/'saved-review.json')if(S/'saved-review.json').exists()else None,'wrapper_sha256':sha(__file__),'scope':'Reviewed saved metadata reader only; no proof compiler, producer, archived executable or canonical mutation.'};(S/'saved-reader-actual.json').write_text(json.dumps(a,indent=2)+'\n');assert a['status']=='PASS_SAVED_READER_OUTER',a;print('PASS',a['review_sha256'],a['seconds'])
