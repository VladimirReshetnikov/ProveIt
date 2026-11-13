#!/usr/bin/env python3
"""Compare all AQ16 policy reports against the guarded author run."""
import hashlib
import json
import re
from pathlib import Path

if not __debug__: raise RuntimeError('optimized Python is unsupported')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TRIAL = ROOT / 'reviews/ipra-aq16-guarded-author'
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
policy_path = HERE / 'task-policy.json'
manifest_path = HERE.parent / 'author-additions.json'
state_path = TRIAL / 'state.json'
inputs = [Path(__file__), policy_path, manifest_path, state_path]
logs = sorted((TRIAL / 'logs').glob('*.log'))
inputs.extend(logs)
before = {str(p.resolve()): H(p) for p in inputs}
assert H(policy_path) == '6a9ed8f9b512752d5a9bfc6589bf093b58ab1e34b900112c082561f0567d5daa'
assert H(manifest_path) == '081e343d107f6ff1e73b1bfded119dd3698f363169ae24c25a07b60ddff33a0d'
assert H(state_path) == 'f6b287f2857c050fd2fdfafa4501853cf41bfd5b15bfc2b0d8ff0cf9884514bd'
policy = json.loads(policy_path.read_text())
manifest = json.loads(manifest_path.read_text())
state = json.loads(state_path.read_text())
order = manifest['order']
assert len(order) == 52 and policy['addition_order'] == order == [r['module'] for r in state['rows']]
assert policy['sources'] == manifest['sources'] and policy['target'] == order[-1]
expected = {name: manifest['axiom_reports'].get(name, []) for name in order}
assert policy['expected_axiom_by_module'] == expected
assert policy['expected_axiom_names'] == expected[order[-1]] and len(expected[order[-1]]) == 3
assert sum(map(len, expected.values())) == 127 and sum(bool(v) for v in expected.values()) == 41
pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
for i, row in enumerate(state['rows']):
    files = list((TRIAL / 'logs').glob(f'{i:03d}-*.log'))
    assert len(files) == 1 and H(files[0]) == row['log_sha256'] and row['exit'] == 0
    reports = pattern.findall(files[0].read_text())
    assert [name for name, _ in reports] == expected[row['module']]
    assert [list(x) for x in reports] == row['axiom_reports']
    for _, axioms in reports:
        assert set(filter(None, re.split(r'\s*,\s*', axioms.strip()))) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert len(logs) == 52 and {str(p.resolve()): H(p) for p in inputs} == before
result = {'status': 'PASS_AQ16_AUTHOR_POLICY_LOG_PREFLIGHT', 'inputs_sha256': before,
          'modules': 52, 'diagnostics': 127, 'target_diagnostics': 3,
          'scope': 'Finite policy/log comparison only; no Lean replay or matched extension.'}
out = HERE / 'policy-preflight-receipt.json'
if out.exists() or out.is_symlink(): raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(result['status'], H(out))
