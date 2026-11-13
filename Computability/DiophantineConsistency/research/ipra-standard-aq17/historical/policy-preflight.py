#!/usr/bin/env python3
"""Compare all AQ17 policy reports against the guarded author run."""
import hashlib
import json
import re
from pathlib import Path

if not __debug__: raise RuntimeError('optimized Python is unsupported')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TRIAL = ROOT / 'reviews/ipra-aq17-guarded-author'
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
policy_path = HERE / 'task-policy.json'
manifest_path = HERE.parent / 'author-additions.json'
state_path = TRIAL / 'state.json'
inputs = [Path(__file__), policy_path, manifest_path, state_path]
logs = sorted((TRIAL / 'logs').glob('*.log'))
inputs.extend(logs)
before = {str(p.resolve()): H(p) for p in inputs}
assert H(policy_path) == '516dff5fdda1544558cb2d3b77987165854cbe53390c7b31f3f221aeae1f75ba'
assert H(manifest_path) == '96cd989a4abaf88c0c181e14a72946b3af1b58f4efc485a63ff1687c56918378'
assert H(state_path) == '0ac4cf0425d3a405fdd6bdf5450d6a7602fb8a15479f26547ec68f739c09b3f7'
policy = json.loads(policy_path.read_text())
manifest = json.loads(manifest_path.read_text())
state = json.loads(state_path.read_text())
order = manifest['order']
assert len(order) == 44 and policy['addition_order'] == order == [r['module'] for r in state['rows']]
assert policy['sources'] == manifest['sources'] and policy['target'] == order[-1]
expected = {name: manifest['axiom_reports'].get(name, []) for name in order}
assert policy['expected_axiom_by_module'] == expected
assert policy['expected_axiom_names'] == expected[order[-1]] and len(expected[order[-1]]) == 3
assert sum(map(len, expected.values())) == 109 and sum(bool(v) for v in expected.values()) == 34
pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
for i, row in enumerate(state['rows']):
    files = list((TRIAL / 'logs').glob(f'{i:03d}-*.log'))
    assert len(files) == 1 and H(files[0]) == row['log_sha256'] and row['exit'] == 0
    reports = pattern.findall(files[0].read_text())
    assert [name for name, _ in reports] == expected[row['module']]
    assert [list(x) for x in reports] == row['axiom_reports']
    for _, axioms in reports:
        assert set(filter(None, re.split(r'\s*,\s*', axioms.strip()))) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert len(logs) == 44 and {str(p.resolve()): H(p) for p in inputs} == before
result = {'status': 'PASS_AQ17_AUTHOR_POLICY_LOG_PREFLIGHT', 'inputs_sha256': before,
          'modules': 44, 'diagnostics': 109, 'target_diagnostics': 3,
          'scope': 'Finite policy/log comparison only; no Lean replay or matched extension.'}
out = HERE / 'policy-preflight-receipt.json'
if out.exists() or out.is_symlink(): raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(result['status'], H(out))
