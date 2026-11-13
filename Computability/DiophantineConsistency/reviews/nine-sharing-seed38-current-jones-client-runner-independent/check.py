#!/usr/bin/env python3
"""Read-only source/provider overlay checks; no Lean invocation."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-seed38-current-jones-client';base=Path('/tmp/nine-sharing-seed38-weighted-retry-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(q/'run.py')=='1fe708fbcd6b72b4bce8de281fee102aeeb226bd6256a7b280bea6e751b913c3'
assert sha(q/'source-manifest.json')=='9a8e3a85c20440199f28c1f857dfd885cffdee87b2028e41c763fdc947a79b78'
source=q/'src/DiophantineConsistency/SharingSeed38CurrentJones.lean';assert sha(source)=='3a3c2fdb8e9182b6bb1faf26529a3c88283dd981bebad8afc7a089eb17cdaeb0'
st=D/'research/nine-sharing-seed38-weighted-retry/attempt01/state.json';assert sha(st)=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534'
s=json.loads(st.read_text());assert s['status']=='PASS' and len(s['rows'])==10
for r in s['rows']:
 n=r['module'];assert r['deps']['exit']==r['compile']['exit']==0
 assert sha(base/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(base/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 assert str(base/'lib/DiophantineConsistency'/(n+'.olean')) not in s['overlay_links']
assert str(base/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean') not in s['overlay_links']
print(json.dumps({'status':'PASS_SOURCE_AND_BASE_OBJECT_CHECK_ONLY','runner_sha256':sha(q/'run.py'),'source_sha256':sha(source),'base_state_sha256':sha(st),'base_modules':len(s['rows']),'scope':'No Lean compile, complete transitive provider check or all-model current-equation bridge.'},indent=2,sort_keys=True))
