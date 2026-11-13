#!/usr/bin/env python3
"""Check exact static-to-seed retry deltas without launching Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];a=D/'research/nine-sharing-norm38-static-to-seed-check';b=D/'research/nine-sharing-norm38-static-to-seed-retry01';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in [(b/'run.py','4bb7ee984f622a3440061f2c86eceb9abdc42a81a7431df23369f05537e6579f'),(b/'source-manifest.json','413cc42a039b8d215ce9ad144319b32629823f925f7436dbbd8c34e214cfbe50'),(b/'src/DiophantineConsistency/Norm38StaticToSeed.lean','8bf928814dc96ba30c7ae8fc6c0edb0db967821c86d785cb51876406a10b7b25')]:assert sha(p)==h
old=(a/'src/DiophantineConsistency/Norm38StaticToSeed.lean').read_text();new=(b/'src/DiophantineConsistency/Norm38StaticToSeed.lean').read_text();before='  simpa [residualAt, residuals, hj] using hi';after='  have hget : residualAt p i = e := by\n    change (residuals p).get ⟨j.val, _⟩ = e\n    exact hj\n  simpa only [hget] using hi';assert old.count(before)==1 and old.replace(before,after)==new
old=(a/'run.py').read_text();new=(b/'run.py').read_text();assert old.replace('/tmp/nine-sharing-norm38-static-to-seed-check-20261105','/tmp/nine-sharing-norm38-static-to-seed-retry01-20261105').replace('a47bdf954ba6520400957a10e71f9c4185f0535499fdf183e54c310146c6ca5d','413cc42a039b8d215ce9ad144319b32629823f925f7436dbbd8c34e214cfbe50')==new
prior=D/'reviews/nine-sharing-norm38-static-to-seed-terminal-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(prior/'result.json').read_bytes()
base=Path('/tmp/nine-sharing-norm38-forward-prefix-check-20261105/lib/DiophantineConsistency/Norm38StaticToSeed.olean');assert not os.path.lexists(base)
print(json.dumps({'status':'PASS_STATIC_TO_SEED_RETRY_DELTA_ONLY','source_sha256':sha(b/'src/DiophantineConsistency/Norm38StaticToSeed.lean'),'runner_sha256':sha(b/'run.py'),'scope':'Source/runner delta, earlier failed evidence and current output collision only; no Lean retry or bridge proof.'},indent=2,sort_keys=True))
