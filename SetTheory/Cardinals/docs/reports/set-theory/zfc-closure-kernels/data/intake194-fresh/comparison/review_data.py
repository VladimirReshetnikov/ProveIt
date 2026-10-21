#!/usr/bin/env python3
"""Own inert data comparison. Does not import or execute archive code."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
NEW = Path('/tmp/zfc-intake194/extracted/K217_Exposed_Marker')
OLD = Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k217')
OWN = Path('/tmp/zfc-intake192-independent-helper')
inputs = {}

def read(p):
    raw = p.read_bytes()
    inputs[str(p)] = {'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)}
    return raw

def obj(p):
    return json.loads(read(p))

def table(p):
    rows = {}
    start = []
    for line in read(p).decode('ascii').splitlines():
        if line.startswith('#! start '):
            start.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q, b, w, d, target = line.split()
            key = int(q), int(b)
            assert key not in rows and d in ('L', 'R')
            rows[key] = int(w), d, int(target)
    states = {q for q, _ in rows}
    assert start == [0]
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert all(w in (0, 1) for w, _, _ in rows.values())
    missing = {t for _, _, t in rows.values()} - states
    assert len(missing) == 1
    return rows, states, missing.pop()

def renamed(rows, mapping):
    return {(mapping[q], b): (w, d, mapping[t])
            for (q, b), (w, d, t) in rows.items()}

identities = []
for new_name, own_name in (
        ('k217.native.tm', 'candidate025-fold217.native.tm'),
        ('prefold218.native.tm', 'candidate025-prefold218.native.tm'),
        ('sites217.json', 'candidate025.sites.json')):
    a, b = NEW/'machine'/new_name, OWN/own_name
    assert read(a) == read(b)
    identities.append({'new': str(a), 'own': str(b), 'exact_bytes': True})

new, states, halt = table(NEW/'machine/k217.native.tm')
old, old_states, old_halt = table(OLD/'k217.native.tm')
assert len(states) == len(old_states) == 217 and halt == old_halt == 254
mapping = {q: q for q in states | {halt}}
mapping.update({188: 213, 213: 210, 210: 188})
assert set(mapping.values()) == old_states | {old_halt}
assert renamed(new, mapping) == old and mapping[0] == 0

new_dense, new_dense_states, new_dense_halt = table(NEW/'machine/k217.tm')
old_dense, old_dense_states, old_dense_halt = table(OLD/'k217.tm')
nm = {int(k): v for k, v in obj(NEW/'machine/canonicalization.json')['mapping'].items()}
om = {int(k): v for k, v in obj(OLD/'canonicalization.json')['native_to_canonical'].items()}
assert renamed(new, nm) == new_dense
assert renamed(old, om) == old_dense
canonical_map = {nm[q]: om[mapping[q]] for q in mapping}
assert renamed(new_dense, canonical_map) == old_dense
assert new_dense_halt == old_dense_halt == 217
assert new_dense_states == old_dense_states == set(range(217))
# Independently confirm the new dense numbering is breadth first, bit zero first.
order = [0]
seen = {0}
for q in order:
    for b in (0, 1):
        target = new[q, b][2]
        if target != halt and target not in seen:
            seen.add(target)
            order.append(target)
assert len(order) == 217 and all(nm[q] == i for i, q in enumerate(order))

source_raw = read(NEW/'machine/sites217.json')
assert source_raw == read(OLD/'sites217.json')
rows = json.loads(source_raw)
leaves = {p: (op, n) for p, op, n in rows}
assert len(leaves) == len(rows) == 4751
prefixes = {p[:i] for p in leaves for i in range(len(p) + 1)}
types = set()
def visit(p):
    if p in leaves:
        t = ('leaf', *leaves[p])
        out = [[p, *leaves[p]]]
    else:
        assert p+'0' in prefixes and p+'1' in prefixes
        a, ar = visit(p+'0')
        b, br = visit(p+'1')
        t, out = ('node', a, b), ar+br
    types.add(t)
    return t, out
tree, expanded = visit('')
assert expanded == rows and len(prefixes) == 9501 and len(types) == 203

baseline, base_states, base_halt = table(NEW/'machine/baseline218.native.tm')
prefold, prefold_states, prefold_halt = table(NEW/'machine/prefold218.native.tm')
assert len(base_states) == len(prefold_states) == 218
assert base_halt == prefold_halt == 254
changed_prefold = [{'row': list(k), 'before': list(baseline[k]), 'after': list(prefold[k])}
                   for k in sorted(baseline) if baseline[k] != prefold[k]]
assert [r['row'] for r in changed_prefold] == [[188, 0], [188, 1], [201, 0], [210, 0]]
assert prefold_states - states == {400} and not states - prefold_states
changed_retained = [{'row': list(k), 'before': list(baseline[k]), 'after': list(new[k])}
                    for k in sorted(new) if baseline[k] != new[k]]
assert len(changed_retained) == 6
assert [(k, v) for k, v in sorted(prefold.items()) if v[2] == 69] == [((53, 1), (1, 'R', 69))]
assert [(k, v) for k, v in sorted(prefold.items()) if v[2] == 400] == [((224, 0), (0, 'R', 400))]
assert new[69, 0] == (0, 'L', 188)
assert new[188, 0] == (0, 'R', 92) and new[188, 1] == (1, 'R', 90)
assert new[92, 0] == (0, 'R', 104) and new[90, 0] == (0, 'R', 105)
assert new[69, 1] == prefold[69, 1] == prefold[400, 1] == (1, 'R', 31)

for p in (NEW/'README.md', NEW/'code/construct217.py', OWN/'arrival192-comparison.json',
          OWN/'candidate025-result.json', Path('/tmp/zfc-intake192/fresh1/actual.json'),
          Path('/tmp/zfc-intake192/fresh1/actual-review.json')):
    read(p)
read(Path(__file__))
result = {
    'status': 'EXACT_CANDIDATE025_AND_ACCEPTED217_ISOMORPHISM_PASS',
    'reviewer': 'opening_encoder; author of the earlier independent candidate025, disclosed',
    'method': 'Own standard-library read-only parser; no supplied code, compiler, runtime, or manifest suite executed.',
    'exact_byte_identities': identities,
    'native_to_accepted_nonidentity_mapping': {'188': 213, '213': 210, '210': 188},
    'all_other_native_labels_fixed': True,
    'native_rows_checked': 434,
    'canonical_rows_checked': 434,
    'canonical_to_accepted_mapping': canonical_map,
    'start_and_halt_preserved': True,
    'source': {'exact_bytes_equal_to_accepted': True, 'leaves': 4751,
               'internal_prefix_roles': 4750, 'dag_nodes': 203, 'maximum_depth': 45,
               'maximum_zero_run': 6,
               'scope': 'Identical complete source gives identical logical roles; complete transition isomorphism transports every tape trajectory and the previously established role binding.'},
    'prefold_changes': changed_prefold,
    'final_changed_retained_rows_vs_baseline218': changed_retained,
    'deleted_state': 400,
    'fold': {'keeper': 69, 'new_helper': 188, 'accepted_helper': 213,
             'marker0_target': 104, 'marker1_target': 105, 'shared_read1_target': 31},
    'conclusion': 'Same 218-to-217 saving. It cannot be stacked with accepted candidate-k217 or candidate025. Dense table bytes differ only because the new packet uses BFS numbering.',
    'existing_runtime_scope': 'Prior accepted192 actual and review are pinned as provenance. No new runtime replay or fresh full-runtime claim is made by this comparison.',
    'appendix_scope': 'Fixed1,3-core appendix is separate theory/source material under peer review; this table comparison makes no calibration or machine claim for that appendix.',
    'findings': [],
    'inputs': inputs,
}
(HERE/'review.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps({'status': result['status'], 'review_sha256': hashlib.sha256((HERE/'review.json').read_bytes()).hexdigest(), 'inputs': len(inputs)}))
