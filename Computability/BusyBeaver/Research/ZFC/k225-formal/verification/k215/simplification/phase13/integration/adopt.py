from pathlib import Path
import json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=Path('/tmp/k215-phase13-root');D=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase13/integration'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.loads((P/'adoption-plan.json').read_text());actual=json.loads((P/'root-actual-review.json').read_text());assert actual['status']=='PASS_ROOT_RAW_PHASE13_ACTUAL'
assert actual['primary']['result_sha256']=='00a44b3ce690bfcd397f53275c2dcec69d25423de8e029086b0aefe020fb397e' and actual['compatibility']['result_sha256']=='bd9e50bce1c8a463719d83c201f402dad3edd89c0621ae827082b75638a3c74f'
peer=Path('/tmp/k215-phase13-runner-peer/compatibility-actual-review.json');assert sha(peer)=='2b316ccb1e81b32bae9f9bff8e2f58d9722c64a818453bbf7f077641f2048f8c'
for x in plan['files']:
 assert sha(R/x['target'])==x['before_sha256'] and sha(R/x['archived_before'])==x['before_sha256'] and sha(x['source'])==x['sha256']
for x in plan['files']:(R/x['target']).write_bytes(Path(x['source']).read_bytes())
for x in plan['files']:assert sha(R/x['target'])==x['sha256']
record={'status':'EXACT_CHECKED_PHASE13_ADOPTION','files':plan['files'],'primary_result_sha256':actual['primary']['result_sha256'],'compatibility_result_sha256':actual['compatibility']['result_sha256'],'root_actual_review_sha256':sha(P/'root-actual-review.json'),'compatibility_peer_sha256':sha(peer),'scope':'Two exact compiled Lean files, synchronized own maintained producer and ancestry input; exact upstream research renderer imported as inert data. No compiler or producer execution during this copy, no machine or Rocq change.'}
(P/'adoption.json').write_text(json.dumps(record,indent=2)+'\n');(D/'adoption.json').write_bytes((P/'adoption.json').read_bytes());print('PASS five exact checked adoptions')
