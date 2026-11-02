#!/usr/bin/env python3
"""Independent finite policy, author-log, and endpoint-source consistency check."""
import copy
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
HIST = BASE / 'research/ipra-standard-current14/historical'
TRIAL = BASE / 'reviews/ipra-standard-current14-author-trial'
digest = lambda b: hashlib.sha256(b).hexdigest()
policy_bytes = (HIST / 'task-policy.json').read_bytes()
manifest_bytes = (HIST.parent / 'author-additions.json').read_bytes()
state_bytes = (TRIAL / 'state.json').read_bytes()
policy, manifest, state = map(json.loads, (policy_bytes, manifest_bytes, state_bytes))
expected = [
    'DiophantineConsistency.IPRAStandardTheory.leibniz',
    'DiophantineConsistency.IPRAStandardTheory.provable_iff',
    'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency',
    'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency',
]
pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)

def verify(p, m, s):
    order = p['addition_order']
    if len(order) != 16 or len(set(order)) != 16 or order != m['order'] or order != [r['module'] for r in s['rows']]:
        raise ValueError('inconsistent module order')
    if p['sources'] != m['sources'] or set(p['sources']) != set(order):
        raise ValueError('inconsistent source metadata')
    if p['target'] != order[-1] or p['expected_axiom_names'] != expected:
        raise ValueError('inconsistent target diagnostics')
    required = {name: (expected if name == order[-1] else []) for name in order}
    if p['expected_axiom_by_module'] != required or {n: m['axiom_reports'].get(n, []) for n in order} != required:
        raise ValueError('inconsistent per-module diagnostics')
    reports = []
    for i, row in enumerate(s['rows']):
        module = row['module']
        logs = list((TRIAL / 'logs').glob(f'{i:03d}-*.log'))
        if len(logs) != 1 or row['exit'] != 0 or row['source_sha256'] != p['sources'][module]['sha256']:
            raise ValueError('inconsistent author row')
        content = logs[0].read_bytes()
        if digest(content) != row['log_sha256']:
            raise ValueError('author log drift')
        parsed = pattern.findall(content.decode())
        if [x[0] for x in parsed] != required[module] or [list(x) for x in parsed] != row['axiom_reports']:
            raise ValueError('inconsistent author axiom reports')
        if any('sorryAx' in ax or set(re.split(r'\s*,\s*', ax.strip())) - {'propext', 'Classical.choice', 'Quot.sound'} for _, ax in parsed):
            raise ValueError('unexpected author axiom')
        reports.extend(parsed)
    endpoint = ROOT / p['sources'][order[-1]]['workspace_path']
    source = endpoint.read_bytes()
    if digest(source) != p['sources'][order[-1]]['sha256']:
        raise ValueError('endpoint source drift')
    printed = re.findall(r'^#print axioms\s+(\S+)\s*$', source.decode(), re.M)
    if printed != expected:
        raise ValueError('endpoint source diagnostics differ')
    return len(reports)

assert digest(policy_bytes) == 'aed46974c461c626aa93781e5e927fb1b63b93d92c51202343ea0e2e3ef08413'
assert digest(manifest_bytes) == '005af2258215bedb54a8f0589eaf898a2b80c6cfa443ce8fa48621cea40b022a'
assert digest(state_bytes) == 'bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61'
assert verify(policy, manifest, state) == 4
for change in ('missing_report', 'wrong_module', 'author_drift'):
    p, m, s = copy.deepcopy(policy), copy.deepcopy(manifest), copy.deepcopy(state)
    if change == 'missing_report': p['expected_axiom_by_module'][p['target']].pop()
    if change == 'wrong_module': p['addition_order'][0] = p['addition_order'][1]
    if change == 'author_drift': s['rows'][-1]['log_sha256'] = '0' * 64
    try:
        verify(p, m, s)
    except ValueError:
        pass
    else:
        raise RuntimeError(f'negative control accepted: {change}')
print('PASS_INDEPENDENT_CURRENT14_POLICY 16 modules 4 reports 3 mutation controls')
