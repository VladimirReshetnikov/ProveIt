"""Check literal state counting, renumbering, and the first blank-input root.

This finite initialization computation does not establish nonhalting.
"""
from pathlib import Path
import hashlib
import json
import sys
import independent_runtime as r

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled.')
ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'baseline' / 'rotation240'
old = r.table(BASE / 'zfc_rotation240_old.tm')
new = r.table(BASE / 'zfc_rotation240.tm')
mapping_record = json.loads((BASE / 'renumbering.json').read_text())

working = {q for q, _ in old}
assert len(working) == 240 and len(old) == 480
assert {n for _, _, n in old.values()} - working == {254}
assert {q for q, _ in new} == set(range(240)) and len(new) == 480

# Recover the deterministic rooted transition-graph isomorphism independently.
mapping = {95: 0, 254: 240}
queue = [95]
seen = set()
while queue:
    q = queue.pop()
    if q in seen:
        continue
    seen.add(q)
    for b in (0, 1):
        w, d, n = old[q, b]
        W, D, N = new[mapping[q], b]
        assert (w, d) == (W, D)
        if n in mapping:
            assert mapping[n] == N
        else:
            assert N not in mapping.values()
            mapping[n] = N
        if n != 254:
            queue.append(n)
assert seen == working and len(set(mapping.values())) == 241
assert mapping[96] == 84
assert {int(k): v for k, v in mapping_record['old_to_new'].items()} == mapping

q = 95
h = 0
ones = set()
used = set()
for steps in range(2_000_001):
    # A root has an empty program counter: no one bit before the header.
    # Earlier qualified non-root dispatches are intentionally not stopping points.
    if (steps and r.clean_dispatch(q, h, ones)
            and not any(h <= x < h + 64 for x in ones)):
        break
    assert steps < 2_000_000
    b = int(h in ones)
    w, d, q1 = old[q, b]
    used.add((q, b))
    if w:
        ones.add(h)
    else:
        ones.discard(h)
    h += d
    q = q1
else:
    raise AssertionError('No qualified root within the verification limit')

logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
spares = [1] * 167
gap = 117
expected = {x + h for x in r.frame('', logical, spares, gap)}
assert (steps, q, h, len(ones)) == (409691, 96, -5, 351)
assert ones == expected
result = {
    'status': 'EXACT_TABLE_AND_BLANK_ROOT_PASS',
    'working_states': 240,
    'transition_rows': 480,
    'halt_old': 254,
    'start_old': 95,
    'start_canonical': 0,
    'dispatch_old': 96,
    'dispatch_canonical': 84,
    'literal_graph_isomorphism_checked': True,
    'blank_steps_to_first_qualified_root': steps,
    'state': q,
    'head': h,
    'marker': h - 1,
    'header': h + 64 + gap,
    'logical_registers': logical,
    'spares': spares,
    'additional_gap': gap,
    'one_cells': sorted(ones),
    'zero_exterior': True,
    'startup_rows': sorted(used),
    'sha256': {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
               for name in ['zfc_rotation240.tm', 'zfc_rotation240_old.tm',
                            'sites_logical.json', 'renumbering.json']},
    'scope': 'Exact finite startup and complete reachable rooted transition-graph isomorphism; no nonhalting assertion.'
}
(ROOT / 'validation' / 'baseline_literal_checks.json').write_text(
    json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items()
                  if k not in ('one_cells', 'spares', 'startup_rows')}, indent=2))
