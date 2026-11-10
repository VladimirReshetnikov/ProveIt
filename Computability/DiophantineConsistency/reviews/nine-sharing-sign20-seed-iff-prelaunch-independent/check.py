#!/usr/bin/env python3
"""Review same-input symbolic sign20/sign21 seed equivalence proposal."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign20-seed-iff-check'
draft = research/'nine-sharing-sign20-seed-iff-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = packet/'src/DiophantineConsistency/Sign20SeedExistential.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign20SeedExistential'
assert digest(source) == digest(draft/'Sign20SeedExistential.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',source.read_text(),re.M) == entry['imports'] == ['DiophantineConsistency.Sign20ReverseBridge']
s = source.read_text()
assert '(∃ v : Fin 21 → V, v 0 = x ∧ InternalZero (SharingSeed20Degree20.seed p) v)' in s
assert '∃ v : Fin 22 → V, v 0 = x ∧ InternalZero (SharingSeed21Degree14.seed p) v' in s
assert 'Sign20ZeroBridge.forward p beta v hp0 hz' in s and 'Sign20ZeroBridge.backward p beta v hp0 hz' in s
assert 'simpa [Sign20Coordinate.lift] using hv' in s and 'simpa [Sign20Coordinate.drop] using hv' in s
assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s
upstream = root/'reviews/nine-sharing-sign20-zero-assembly-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(source),'runner_sha256':digest(packet/'run.py'),
                  'scope':'proposed same-input equivalence at symbolic ports, explicit beta representation hypothesis; no endpoint'},sort_keys=True,indent=2))
