#!/usr/bin/env python3
"""Read-only checks of slot-runner pins and inherited output names."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-slot-extraction-check';base=Path('/tmp/nine-sharing-seed38-weighted-retry-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(q/'run.py')=='18f0d37ac3d99bf2148b05522379d5aac8994010cc1a335b3701ce049714a49f'
assert sha(q/'source-manifest.json')=='4936a8eaa5b3b0fdc03f825dcbdf5fb6621e4dff8d88f7547d441dde8238d32f'
src=q/'src/DiophantineConsistency/Norm38SlotExtraction.lean';assert sha(src)==sha(D/'research/nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean')=='7afacc8c1f2b9b0e1b443f346653c21dde511fe200e8296daf2ec2afd4ea38fc'
state=D/'research/nine-sharing-seed38-weighted-retry/attempt01/state.json';assert sha(state)=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534'
s=json.loads(state.read_text());assert s['status']=='PASS' and len(s['rows'])==10
for r in s['rows']:
 n=r['module'];assert r['deps']['exit']==r['compile']['exit']==0
 assert sha(base/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(base/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 assert str(base/'lib/DiophantineConsistency'/(n+'.olean')) not in s['overlay_links']
assert str(base/'lib/DiophantineConsistency/Norm38SlotExtraction.olean') not in s['overlay_links']
print(json.dumps({'status':'PASS_SOURCE_AND_BASE_OBJECT_CHECK_ONLY','runner_sha256':sha(q/'run.py'),'source_sha256':sha(src),'base_modules':10,'scope':'No Lean compile, complete transitive dependency check or model bridge.'},indent=2,sort_keys=True))
