#!/usr/bin/env python3
"""Record later upstream source changes relative to the frozen AQ16 snapshot."""
import hashlib,json,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];snapshot=Path('/tmp/ipra-aq16-historical-paired-run-02/snapshot/manifest.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();m=json.loads(snapshot.read_text())
assert H(snapshot)=='c0a0c9a34bf26f7a24b9864f675eaf22196be2e4c3444975f67d55f79631b13d'
names=('DiscreteOrderedRingFacts','ModelArithmetic','ModelCarrierCurrent','ModelCarrierScaled','ModelDifferenceRing')
changed=subprocess.check_output(['git','diff','--name-only','a6cdf3d85f^1','a6cdf3d85f'],cwd=ROOT,text=True).splitlines()
paths=['Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+n+'.lean' for n in names]
assert all(p in changed for p in paths)
assert all('DiophantineConsistency.'+n not in m['sources'] for n in names)
out={'status':'PASS_AQ16_LATER_UPSTREAM_SOURCE_SCOPE','snapshot_sha256':H(snapshot),'merge_commit':'a6cdf3d85f','later_changed_files':paths,'scope':'These five later upstream files are absent from the frozen AQ16 source manifest; the 15 preparation-time drifts remain as recorded.'};p=HERE/'upstream-snapshot-receipt.json'
if p.exists():raise ValueError('refusing to overwrite receipt')
p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(p))
