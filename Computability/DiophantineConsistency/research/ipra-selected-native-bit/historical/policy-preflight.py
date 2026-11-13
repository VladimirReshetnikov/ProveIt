#!/usr/bin/env python3
"""Compare all SELECTED_NATIVE_BIT policy reports against the guarded author run."""
import hashlib
import json
import re
from pathlib import Path

if not __debug__: raise RuntimeError('optimized Python is unsupported')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TRIAL = ROOT / 'reviews/ipra-selected-native-bit-guarded-author'
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
policy_path = HERE / 'task-policy.json'
manifest_path = HERE.parent / 'author-additions.json'
state_path = TRIAL / 'state.json'
inputs = [Path(__file__), policy_path, manifest_path, state_path]
logs = sorted((TRIAL / 'logs').glob('*.log'))
inputs.extend(logs)
before = {str(p.resolve()): H(p) for p in inputs}
assert H(policy_path) == '70923d446875a9a99eb02d4315264cc0eb66837b79e5ace66b9fc12e2313dde9'
assert H(manifest_path) == '7eb9d405153d4de522b3b10007003691de860565a882c1f83e8cd3d589bb2607'
assert H(state_path) == '3bee2db67ca881cf02458d6688f3b8252eab6cc36ce2b7a610d2ef2a84127321'
policy = json.loads(policy_path.read_text())
manifest = json.loads(manifest_path.read_text())
state = json.loads(state_path.read_text())
order = manifest['order']
assert len(order) == 11 and policy['addition_order'] == order == [r['module'] for r in state['rows']]
expected_sources = {name: dict(row) for name, row in manifest['sources'].items()}
for name in ('DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral', 'DiophantineConsistency.IPRASquareSumsNative'):
    expected_sources[name]['workspace_path'] = 'Computability/DiophantineConsistency/Lean/' + name.replace('.', '/') + '.lean'
assert policy['sources'] == expected_sources and policy['target'] == order[-1]
expected = {name: manifest['axiom_reports'].get(name, []) for name in order}
assert policy['expected_axiom_by_module'] == expected
assert policy['expected_axiom_names'] == expected[order[-1]] and len(expected[order[-1]]) == 2
assert sum(map(len, expected.values())) == 18 and sum(bool(v) for v in expected.values()) == 5
pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
for i, row in enumerate(state['rows']):
    files = list((TRIAL / 'logs').glob(f'{i:03d}-*.log'))
    assert len(files) == 1 and H(files[0]) == row['log_sha256'] and row['exit'] == 0
    reports = pattern.findall(files[0].read_text())
    assert [name for name, _ in reports] == expected[row['module']]
    assert [list(x) for x in reports] == row['axiom_reports']
    for _, axioms in reports:
        assert set(filter(None, re.split(r'\s*,\s*', axioms.strip()))) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert len(logs) == 11 and {str(p.resolve()): H(p) for p in inputs} == before
result = {'status': 'PASS_SELECTED_NATIVE_BIT_AUTHOR_POLICY_LOG_PREFLIGHT', 'inputs_sha256': before,
          'modules': 11, 'diagnostics': 18, 'target_diagnostics': 2,
          'scope': 'Finite policy/log comparison only; no Lean replay or matched extension.'}
out = HERE / 'policy-preflight-receipt.json'
if out.exists() or out.is_symlink(): raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(result['status'], H(out))
