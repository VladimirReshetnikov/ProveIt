#!/usr/bin/env python3
"""Review same-input symbolic sign21/sign22 seed equivalence proposal."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign21-seed-iff-check'
draft = research/'nine-sharing-sign21-seed-iff-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = packet/'src/DiophantineConsistency/Sign21SeedExistential.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign21SeedExistential'
assert digest(source) == digest(draft/'Sign21SeedExistential.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',source.read_text(),re.M) == entry['imports'] == ['DiophantineConsistency.Sign21ReverseBridge']
s = source.read_text()
assert '(∃ v : Fin 22 → V, v 0 = x ∧ InternalZero (SharingSeed21Degree14.seed p) v)' in s
assert '∃ v : Fin 23 → V, v 0 = x ∧ InternalZero (SharingSeed22Dodecic.seed p) v' in s
assert 'Sign21ZeroBridge.forward p v hz' in s and 'Sign21ZeroBridge.backward p v hz' in s
assert 'simpa [Sign21Coordinate.lift] using hv' in s and 'simpa [Sign21Coordinate.drop] using hv' in s
assert 'hp0' not in s
upstream = root/'reviews/nine-sharing-sign21-zero-assembly-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(source),'runner_sha256':digest(packet/'run.py'),
                  'scope':'proposed same-input equivalence at symbolic ports, no beta cast or endpoint'},sort_keys=True,indent=2))
