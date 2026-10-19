#!/usr/bin/env python3
"""Reconstruct the combined 238-state table and check its exact blank prefix.

No finite run is used as evidence for universal runtime equivalence.  That
obligation has a separate affine/list symbolic certificate.  This script
checks exact input pins, literal composition, complete transition census,
renumbering, and the finite initialization by two independent interpreters.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O or -OO.')
ROOT = Path(__file__).resolve().parent
START, DISPATCH, HALT = 95, 96, 254
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
PINS = {
    'zfc_boundary239.tm': '666f5bf1370b6b44ff4e614e4b194bc5be6b4c621914842ad7e344d6570a544e',
    'zfc_boundary239_old.tm': 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719',
    'zfc239.tm': '4447a2423907f2b96e8bcd6c88ed2d1e353f925fb8cf36ca913224ddce5914ba',
    'zfc239_old.tm': '76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b',
    'zfc240_old.tm': '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f',
}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in result and b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        result[q, b] = w, d, n
    return result

def encode(t, start):
    return ('#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {n}\n' for (q, b), (w, d, n) in sorted(t.items())
    )).encode()

def delay_erasure(t):
    assert t[147, 0] == (0, 'R', 169)
    assert t[80, 0] == (0, 'R', 25)
    assert t[91, 1] == (0, 'L', 50)
    assert [key for key, row in t.items() if row[2] == 169] == [(147, 0)]
    out = {key: (w, d, 80 if n == 169 else n)
           for key, (w, d, n) in t.items() if key[0] != 169}
    out[80, 0] = (0, 'L', 106)
    out[91, 1] = (1, 'L', 167)
    return out

def sparse(t, start, steps):
    q, h, ones = start, 0, set()
    counts = Counter()
    minimum = maximum = 0
    for _ in range(steps):
        b = int(h in ones)
        counts[q, b] += 1
        w, d, q = t[q, b]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += 1 if d == 'R' else -1
        minimum, maximum = min(minimum, h), max(maximum, h)
    return (q, h, sorted(ones)), counts, (minimum, maximum)

def dense(t, start, steps):
    offset = steps + 1
    cells = bytearray(2 * steps + 3)
    p, q = offset, start
    for _ in range(steps):
        w, d, q = t[q, cells[p]]
        cells[p] = w
        p += 1 if d == 'R' else -1
    return q, p - offset, [i - offset for i, b in enumerate(cells) if b]

def save(name, data):
    (ROOT / name).write_text(json.dumps(data, indent=2) + '\n')

def main():
    for name, expected in PINS.items():
        assert digest((ROOT / 'inputs' / name).read_bytes()) == expected, name
    baseline = table(ROOT / 'inputs/zfc240_old.tm')
    delayed = table(ROOT / 'inputs/zfc239_old.tm')
    boundary = table(ROOT / 'inputs/zfc_boundary239_old.tm')
    assert delay_erasure(baseline) == delayed
    assert len(boundary) == 478 and 218 not in {q for q, _ in boundary}
    combined = delay_erasure(boundary)
    working = {q for q, _ in combined}
    assert len(working) == 238 and 169 not in working and 218 not in working
    assert set(combined) == {(q, b) for q in working for b in (0, 1)}
    assert {row[2] for row in combined.values()} - working == {HALT}
    order = [START] + sorted(working - {START})
    mapping = {q: i for i, q in enumerate(order)} | {HALT: 238}
    canonical = {(mapping[q], b): (w, d, mapping[n])
                 for (q, b), (w, d, n) in combined.items()}
    old_bytes, canonical_bytes = encode(combined, START), encode(canonical, 0)
    assert digest(old_bytes) == '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
    assert digest(canonical_bytes) == '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'
    (ROOT / 'zfc_combined238_old.tm').write_bytes(old_bytes)
    (ROOT / 'zfc_combined238.tm').write_bytes(canonical_bytes)
    assert table(ROOT / 'zfc_combined238.tm') == canonical
    reached, todo = set(), [START]
    while todo:
        q = todo.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != HALT:
            todo.extend(combined[q, b][2] for b in (0, 1))
    assert reached == working | {HALT}
    save('renumbering.json', {'old_to_new': mapping, 'new_to_old': order + [HALT],
                            'start': 0, 'halt': 238, 'dispatch': mapping[DISPATCH]})

    # Complete finite startup certificate, deliberately independent of any
    # induction claim about subsequent source execution.
    ref, counts, _ = sparse(boundary, START, 409691)
    original, _, _ = sparse(baseline, START, 409691)
    actual, new_counts, head_range = sparse(combined, START, 409835)
    independent = dense(combined, START, 409835)
    relabeled = dense(canonical, 0, 409835)
    assert original == ref == actual == independent
    assert relabeled == (mapping[actual[0]], actual[1], actual[2])
    assert actual[0] == DISPATCH and actual[1] == -5 and len(actual[2]) == 351
    keys = [(80, 0), (169, 0), (169, 1), (91, 1)]
    assert [counts[key] for key in keys] == [18, 12, 6, 3]
    assert sum(counts[key] * delta for key, delta in zip(keys, (4, 2, 4, 8))) == 144
    assert all(counts[key] == 0 for key in counts if key[0] in (179, 218, 223, 237))
    on = set(actual[2])
    head = actual[1]
    assert min(on) == head - 1
    header = min(x for x in on if x >= head)
    values, p = [], header + 1
    while p <= max(on):
        assert p not in on and p + 1 in on
        start = p + 1
        p = start
        while p in on:
            p += 1
        values.append(p - start - 1)
    logical = [values[i] for i in PHY]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert len(values[9:]) == 167 and set(values[9:]) == {1}
    assert header - head - 64 == 117
    save('blank_prefix.json', {
        'status': 'EXACT_SPARSE_DENSE_AND_CANONICAL_AGREEMENT',
        'steps': 409835, 'old_boundary_steps': 409691, 'added_steps': 144,
        'initial_state': 0, 'initial_head': 0, 'initial_tape': 'all zero',
        'final_state': mapping[DISPATCH], 'final_state_old': DISPATCH,
        'final_head': head, 'marker': head - 1, 'header': header,
        'additional_gap': 117, 'pc': '', 'logical_registers': logical,
        'physical_registers': values[:9], 'spare_values': values[9:],
        'all_one_positions': actual[2], 'all_other_cells_zero': True,
        'one_count': len(on), 'head_range': head_range,
        'clock_counts': [{'state': key[0], 'read': key[1], 'count': counts[key]}
                         for key in keys],
        'complete_configuration_equals_boundary239_and_rotation240': True,
    })
    changes = [{'state': q, 'read': b, 'old': boundary.get((q, b)),
                'new': combined.get((q, b))}
               for q, b in sorted(set(boundary) | set(combined))
               if boundary.get((q, b)) != combined.get((q, b))]
    result = {
        'status': 'EXACT_CONSTRUCTION_AND_STARTUP_PASS',
        'working_states': 238, 'transition_rows': 476, 'separate_halt_outcomes': 1,
        'symbols': [0, 1], 'blank': 0, 'moves': ['L', 'R'],
        'start': 0, 'dispatch': mapping[DISPATCH], 'halt': 238,
        'canonical_sha256': digest(canonical_bytes),
        'inherited_label_sha256': digest(old_bytes),
        'all_working_states_graph_reachable': True,
        'exact_startup_steps': 409835, 'input_pins': PINS,
        'table_changes_from_boundary239': changes,
        'scope': 'Exact composition, renumbering, and finite startup; subsequent runtime uses the separate universal certificate.',
    }
    save('construction.json', result)
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
