"""Read-only independent binding of the current BinderAbsorption supplement."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
P = D / 'research/arithmetic-current-hierarchy2011-cache-plan.json'
S = D / 'research/arithmetic-current-hierarchy2011-current-supplement.json'
B = D / 'reviews/arithmetic-current-hierarchy2011-plan-peer-audit.json'
O = D / 'reviews/arithmetic-current-hierarchy2011-supplement-peer-audit.json'
seen = []
def record(p):
    b = Path(p).read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
def check(p):
    a = record(p['path'])
    assert a['sha256'] == p['sha256'], p['path']
    assert 'bytes' not in p or a['bytes'] == p['bytes'], p['path']
    seen.append(a)
    return a
assert not O.exists()
sp = check(dict(path=str(S), sha256='079d66899d794f1ea17dfa1cd4ff940763b273d8e16d6032060654687ee65549'))
s = json.loads(S.read_text())
p = json.loads(P.read_text())
check(s['frozen_plan'])
b = json.loads(B.read_text())
check(b['plan'])
check(b['manifest'])
check(b['driver'])
assert b['status'] == 'FROZEN_SNAPSHOT_PASS_CURRENT_SOURCE_REVALIDATION_REQUIRED'
assert len(b['live_source_drift']) == 1
assert b['live_source_drift'][0] == dict(expected=s['previous_source'], actual=s['current_source'])
module = next(m for m in p['modules'] if m['module'] == s['module'])
assert module['mode'] == 'FRESH_CURRENT_SOURCE_REQUIRED' and module['objects'] == []
assert module['source'] == s['previous_source']
assert s['unchanged_counts'] == p['counts']
for k in ['current_source', 'historical_snapshot', 'complete_diff', 'script']:
    check(s[k])
rel = str(Path(s['current_source']['path']).relative_to(R))
old = subprocess.check_output(['git', 'show', p['snapshot_head'] + ':' + rel], cwd=R)
new = subprocess.check_output(['git', 'show', s['snapshot_head'] + ':' + rel], cwd=R)
assert old == Path(s['historical_snapshot']['path']).read_bytes()
assert new == Path(s['current_source']['path']).read_bytes()
diff = subprocess.check_output(['git', 'diff', p['snapshot_head'], s['snapshot_head'], '--', rel], cwd=R)
assert diff == Path(s['complete_diff']['path']).read_bytes()
# This file has its two ordinary imports before its first namespace/declaration.
lines = new.decode().splitlines()
imports = ['Init'] + [x for line in lines for x in re.findall(r'^(?:public )?import\s+(\S+)\s*$', line)]
assert imports == s['unchanged_imports'] == module['imports']
wanted = {x['path']: x for x in p['pins']}
assert len(wanted) == len(p['pins']) == 2259
wanted[s['current_source']['path']] = s['current_source']
actual = {x['path']: x for x in s['comparisons']}
assert len(actual) == len(s['comparisons']) == s['comparison_count'] == 2259
assert actual == wanted
for row in actual.values():
    check(row)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
assert head == s['snapshot_head']
result = dict(status='PASS_CURRENT_SUPPLEMENT_BOUND_NO_COMPILER', supplement=sp,
    baseline_audit=record(B), driver=record(__file__), current_head=head,
    comparisons=len(seen), unique_paths=len({r['path'] for r in seen}), counts=p['counts'],
    finding='Only already-fresh BinderAbsorption changed; all cached sources, all 983 providers and the exact 92-refresh descendant set remain as independently audited.',
    observations=seen)
O.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'observations'}, indent=2))
