#!/usr/bin/env python3
"""Finite witness that the naive zero-spare patch enters a permanent drift.

The unmodified accepted machines are untouched. Run in a copy of the packet
if retaining SHA256SUMS after regenerating the receipt is required.
"""
from pathlib import Path
import hashlib, json, sys
assert __debug__ and not sys.flags.optimize
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
source = ROOT / 'references/parent/pa194CS.native.tm'
rows = {}
for line in source.read_text().splitlines():
    q, b, w, d, n = line.split()
    rows[int(q), int(b)] = int(w), d, int(n)
assert rows[198, 0] == (1, 'L', 40)
rows[198, 0] = (0, 'L', 40)
assert rows[35, 0] == (1, 'R', 35)
state, head, ones, dispatcher_times = 74, 0, set(), []
for time in range(100000):
    assert state != 254
    if state == 84:
        dispatcher_times.append(time)
    if state == 35 and head > max(ones, default=-1):
        break
    w, d, state = rows[state, int(head in ones)]
    (ones.add if w else ones.discard)(head)
    head += 1 if d == 'R' else -1
else:
    raise AssertionError('Expected drift witness was not reached.')
assert dispatcher_times == [38, 66]
receipt = {
    'parent_native_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'single_patch': {'state': 198, 'read': 0, 'old': [1, 'L', 40], 'new': [0, 'L', 40]},
    'dispatcher_times_before_drift': dispatcher_times,
    'first_certified_drift_time': time, 'state': state, 'head': head,
    'ones': sorted(ones), 'all_cells_at_and_right_of_head_are_zero': True,
    'drift_row': [35, 0, 1, 'R', 35],
    'inductive_conclusion': 'Each subsequent step writes1 and moves right into a fresh zero cell in state35. The patched machine never again reaches the source dispatcher.',
    'scope': 'Rejected patch only; neither PA194J nor PA194D uses this change.'}
(HERE / 'zero_spare_bootstrap.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
