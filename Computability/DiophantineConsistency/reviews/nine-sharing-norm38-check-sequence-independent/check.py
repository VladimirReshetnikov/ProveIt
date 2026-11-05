#!/usr/bin/env python3
"""Independent, read-only checks; no Lean invocation."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
Q=D/'research/nine-sharing-norm38-check-sequence'; repo=D.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Q/'run.py')=='3b54daf61b99632815a078a4d4fd6a5dba7b30181045b3e7b2eaf319761fe488'
assert sha(Q/'source-manifest.json')=='860bc118705af6beb8c55f98036605506caa801460b058e4319791faa63304ac'
state=D/'research/nine-current-fresh-jones-client/attempt01/state.json'
assert sha(state)=='469b279c32677e416e757dcd59835ea0514d1e524338d3c451ae8cfa8e446439'
base=json.loads(state.read_text()); manifest=json.loads((Q/'source-manifest.json').read_text())
overlay=Path('/tmp/nine-fresh-jones-client-20261105/lib');seen=set();rows=manifest['rows'];assert len(rows)==6
for row in rows:
 module=row['module'];name=module.split('.')[-1]
 assert sha(Q/'src/DiophantineConsistency'/(name+'.lean'))==row['source_sha256']
 assert sha(repo/row['source'])==row['source_sha256']
 assert all(dep in seen for dep in row['imports'] if dep in {r['module'] for r in rows})
 rel=module.replace('.','/')+'.olean'
 assert not any(Path(k).relative_to(overlay).as_posix()==rel for k in base['overlay_links'])
 seen.add(module)
print(json.dumps({'status':'PASS_SOURCE_AND_OVERLAY_CHECK_ONLY','stages':len(rows),'scope':'No Lean launch, build, complete ancestry or atomic resource guarantee.'},indent=2,sort_keys=True))
