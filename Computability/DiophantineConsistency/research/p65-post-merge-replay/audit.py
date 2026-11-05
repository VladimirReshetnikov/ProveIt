#!/usr/bin/env python3
"""Audit observed output and recheck the two captured provider inventories."""
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing to run with assertions disabled')

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
ROOT = Path('/tmp/p65-post-merge-replay')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


plan = json.loads((ROOT / 'plan.json').read_text())
results = json.loads((ROOT / 'results.json').read_text())
assert len(plan) == len(results) == 8
for p, r in zip(plan, results):
    assert p['module'] == r['module'] and r['exit'] == 0
    assert sha(Path(p['source'])) == p['source_sha256']
    assert sha(Path(p['shim'])) == p['shim_sha256']
    assert sha(Path(r['object'])) == r['object_sha256']
    assert sha(Path(r['log'])) == r['log_sha256']
    text = Path(r['log']).read_text()
    assert not any(x in text for x in ('sorryAx', 'error:', 'warning:'))
    assert not Path(r['object']).is_symlink()

endpoint = Path(results[-1]['log']).read_text()
names = ['positiveBridge', 'native_equivalence', 'standard_equivalence', 'reference_equivalence']
for name in names:
    assert f"'DiophantineConsistency.IPRAPositive65.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in endpoint

inventories = {}
for packet in ('p65-reverse-provider', 'p65-canonical-endpoint-provider'):
    directory = RESEARCH / packet
    manifest = json.loads((directory / 'manifest.json').read_text())
    old = json.loads((directory / 'results.json').read_text())
    for result in old.values():
        assert sha(Path(result['object'])) == result['object_sha256']
    for binding in manifest['bindings'].values():
        assert sha(Path(binding['object'])) == binding['sha256']
    inventories[packet] = {'objects': len(old), 'bindings': len(manifest['bindings'])}

print(json.dumps({'status': 'PASS', 'modules': len(results), 'inventories': inventories,
                  'endpoint_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
                  'scope': 'captured-provider replay; full transitive ancestry inherited'}, indent=2))
