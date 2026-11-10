#!/usr/bin/env python3
"""Fresh prelaunch audit of the sign25 endpoint; performs no Lean calls."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign25-endpoint-check'
old = root / 'research/nine-sharing-sign26-endpoint-retry02/src/DiophantineConsistency'
manifest = json.loads((packet / 'source-manifest.json').read_text())
rows = manifest['rows']
names = ['Sign25NativeExpression', 'Sign25DirectNative', 'Sign25DirectStandard', 'Sign25DirectTranslated']
assert [row['module'] for row in rows] == ['DiophantineConsistency.' + name for name in names]
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {}
for row, name in zip(rows, names):
    src = packet / 'src/DiophantineConsistency' / (name + '.lean')
    draft = root / 'research/nine-sharing-sign25-endpoint-draft' / (name + '.lean')
    previous = old / (name.replace('Sign25', 'Sign26') + '.lean')
    assert digest(src) == digest(draft) == row['source_sha256']
    assert src.read_text() == (previous.read_text().replace('SharingSeed26Sextic', 'SharingSeed25Octic')
                              .replace('Sign26', 'Sign25').replace('Fin 26', 'Fin 25'))
    pins[name] = digest(src)
native = (packet / 'src/DiophantineConsistency/Sign25DirectNative.lean').read_text()
standard = (packet / 'src/DiophantineConsistency/Sign25DirectStandard.lean').read_text()
translated = (packet / 'src/DiophantineConsistency/Sign25DirectTranslated.lean').read_text()
assert 'nativeTheory ⊢' in native and '∼mappedNativeRefutation embedding' in native
assert 'standardTheory ⊢' in standard and '∼mappedNativeRefutation embedding' in standard
assert 'standardTheory ⊢' in translated and '(Semiformula.lMap embedding sourceSentence)ᴺ' in translated
assert not Path('/tmp/nine-sharing-sign25-endpoint-check-20261106').exists()
assert 'Bounded sign26 direct endpoint diagnostic' in (packet / 'run.py').read_text()
result = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'],
                        capture_output=True, text=True, timeout=180)
assert result.returncode == 0 and not result.stderr
assert json.loads(result.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_FRESH_PRELAUNCH', 'lean_called': False,
                  'runner_sha256': digest(packet / 'run.py'),
                  'manifest_sha256': digest(packet / 'source-manifest.json'),
                  'source_sha256': pins, 'preflight_exit': result.returncode,
                  'scope': 'static source and point-in-time provider checks; no endpoint proof or full transitive ancestry',
                  'stale_runner_state_scope': 'sign26 label for sign25 endpoint'}, sort_keys=True, indent=2))
