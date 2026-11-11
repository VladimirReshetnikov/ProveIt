#!/usr/bin/env python3
"""Read-only source and resource survey. It never starts Lean or approves a run."""
import hashlib
import json
import re
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
WORKTREE = HERE.parents[3]
pins = {
    'P73Graph.lean': (PROJECT/'Lean/DiophantineConsistency/Compact44/P73Graph.lean', '37537ef46555cde7a8a1017995988b6ca9ce6a121f07ebe70b0219951758dcac'),
    'IPRAPositive73.lean': (PROJECT/'Lean/DiophantineConsistency/Compact44/IPRAPositive73.lean', 'b62f982919727f25e5a6e14cb6dfdbe80cb602b8b9b346ce3510d3e006920396'),
    'candidate.json': (PROJECT/'research/ordinary13-p73-triangular91-50/p73_rewrite91_30.json', '474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180'),
    'candidate-independent-check.py': (PROJECT/'reviews/ordinary13-p73-triangular90-50-independent/check.py', '70e1159e2d433676d8782c2bf4c983a9a25936ad3067f51c7796e1058f884c19'),
    'candidate-independent-result.json': (PROJECT/'reviews/ordinary13-p73-triangular90-50-independent/result.json', 'e3ee618e93118cf4cfb6bd38cd9abdd76434fc07a000cef5db2437cfa0b233cc'),
    'P73Shared91.lean': (HERE/'P73Shared91.lean', '6fca39ca8af4743a9be256594cd87b2628d6b8c8e87107b08d604556e43bf364'),
    'P73Shared91Model.lean': (HERE/'P73Shared91Model.lean', 'c2aa3ec2a50c714f59bd4c61589e5fd460af2d641ed67111cbaabf2d97ddcdd5'),
    'P73Shared91Endpoint.lean': (HERE/'P73Shared91Endpoint.lean', '7314625ae4cb2a4fb99c607be47f252444c5304d2bfc2c73c75160df820c3746'),
    'make_source.py': (HERE/'make_source.py', '6892107d3070b30718cd7de35f226f968fba194196d477e94b085da645c2b7db'),
}
for label, (path, expected) in pins.items():
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, label

# Compare all 91 gate operations, not just the changed expression. The one
# nested Lean let is expanded as kM; all remaining lets are single gates.
draft = (HERE/'P73Shared91.lean').read_text()
body = draft.split('-- BEGIN LITERAL GRAPH\n', 1)[1].split('  -- END LITERAL GRAPH', 1)[0]
lines = body.splitlines()
pattern = re.compile(r'^  let (\w+) := (\w+|[0-9]+) ([+*\-]) (\w+|[0-9]+)$')
def atom(s): return int(s) if s.isdecimal() else s
rows = []
for line in lines:
    if line == '  let g35 := q3 + k * M':
        rows.extend([['kM', '*', 'k', 'M'], ['g35', '+', 'q3', 'kM']])
    else:
        m = pattern.fullmatch(line)
        assert m, line
        name, left, op, right = m.groups()
        rows.append([name, op, atom(left), atom(right)])
candidate = json.loads(pins['candidate.json'][0].read_text())
assert len(rows) == 91 and rows == candidate['source']
assert candidate['witnesses'] == ['j','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
assert candidate['fixed_numerals'] == ['beta','K0','MC','MF']

# Point observations only. No local object is called authenticated merely
# because it exists. The historical P73 build has no pinned closure here.
provider = WORKTREE/'.lake/build/lib/lean/DiophantineConsistency/Compact44'
objects = {n: (provider/(n+'.olean')).is_file() for n in ('P73Graph','IPRAPositive73')}
free = shutil.disk_usage('/tmp').free
print(json.dumps({
    'source_pins': 'PASS', 'literal_graph_rows_match': len(rows),
    'existing_project_object_observation': objects,
    'tmp_free_bytes': free, 'runtime_disk_stop_bytes': 5100000000,
    'disk_above_stop_at_sample': free > 5100000000,
    'provider_authentication': 'NOT_ESTABLISHED',
    'lean_launch_readiness': 'BLOCKED: no audited provider closure or reviewed guarded runner',
    'scope': 'Read-only point-in-time survey; no Lean run, compilation, proof, or complete ancestry claim.'
}, indent=2, sort_keys=True))
