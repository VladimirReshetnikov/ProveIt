#!/usr/bin/env python3
"""Review the same-input symbolic sign24 seed equivalence proposal."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign24-seed-iff-check'
draft = research / 'nine-sharing-sign24-seed-iff-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = packet / 'src/DiophantineConsistency/Sign24SeedExistential.lean'
entry, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign24SeedExistential'
assert digest(source) == digest(draft / 'Sign24SeedExistential.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M) == entry['imports'] == ['DiophantineConsistency.Sign24ReverseBridge']
s = source.read_text()
assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s
assert '(∃ v : Fin 25 → V, v 0 = x ∧ InternalZero (SharingSeed24Octic.seed p) v)' in s
assert '∃ v : Fin 26 → V, v 0 = x ∧ InternalZero (SharingSeed25Octic.seed p) v' in s
assert 'Sign24ZeroBridge.forward p beta v hp0 hz' in s and 'Sign24ZeroBridge.backward p beta v hp0 hz' in s
assert 'simpa [Sign24Coordinate.lift] using hv' in s and 'simpa [Sign24Coordinate.drop] using hv' in s
upstream = root / 'reviews/nine-sharing-sign24-zero-assembly-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(source),'runner_sha256':digest(packet/'run.py'),
                  'scope':'proposed same-input equivalence under explicit beta cast; no current port or endpoint'},sort_keys=True,indent=2))
