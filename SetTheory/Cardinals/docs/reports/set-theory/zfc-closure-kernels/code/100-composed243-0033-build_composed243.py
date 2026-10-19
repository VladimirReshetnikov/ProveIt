#!/usr/bin/env python3
"""Apply the pinned compensated-state fold to the pinned rotated244 table.

The output is an exact construction, not by itself a semantic certificate.
The source-loop proof and compensated-state simulation are separate premises.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import shutil
import sys

HERE = Path(__file__).resolve().parent
ROTATED_SHA = '0160caaf5d6db52eb7eb97a76cb04db4b424eb2bc0d58617818a6c7c6a1fe776'
BASELINE_SHA = 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
SITES_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def read_table(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, bit, write, move, target = line.split()
            key = int(q), int(bit)
            assert key not in rows
            assert move in ('L', 'R')
            rows[key] = int(write), move, int(target)
    return rows, start


def encode(rows, start):
    return '#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {t}\n' for (q, b), (w, d, t) in sorted(rows.items()))


def main():
    assert __debug__, 'Assertions must be enabled.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rotation', type=Path,
                        default=HERE/'loop_archive/zfc244-loop-rotation-20261018')
    parser.add_argument('--output', type=Path, default=HERE/'composed243')
    parser.add_argument('--boot', action='store_true')
    args = parser.parse_args()
    rotation = args.rotation.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    baseline = rotation/'reference/baseline245'
    assert digest(rotation/'machine/machine_old.tm') == ROTATED_SHA
    assert digest(baseline/'certificate/machine_old.tm') == BASELINE_SHA
    assert digest(rotation/'machine/sites_logical.json') == SITES_SHA
    rows, start = read_table(rotation/'machine/machine_old.tm')
    original, original_start = read_table(baseline/'certificate/machine_old.tm')
    assert start == original_start == 95 and len(rows) == 488
    assert rows[92, 1] == (1, 'L', 24)
    assert rows[104, 1] == rows[106, 1] == (1, 'R', 122)
    assert rows[167, 1] == (1, 'L', 92)
    before = {key: rows[key] for key in ((92, 1), (104, 1), (106, 1), (167, 1))}
    patches = {(92, 1): (1, 'R', 66), (104, 1): (1, 'R', 92),
               (106, 1): (1, 'R', 92), (167, 1): (1, 'L', 151)}
    rows.update(patches)
    del rows[122, 0], rows[122, 1]
    states = {q for q, b in rows}
    assert len(states) == 243 and len(rows) == 486
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert {q for w, d, q in rows.values()} - states == {254}
    assert 26 not in states and 122 not in states
    reached, pending = {95}, [95]
    while pending:
        q = pending.pop()
        if q == 254:
            continue
        for b in (0, 1):
            target = rows[q, b][2]
            if target not in reached:
                reached.add(target)
                pending.append(target)
    assert reached == states | {254}
    assert set(original)-set(rows) == {(26, 0), (26, 1), (122, 0), (122, 1)}
    assert {key for key in rows if rows[key] != original[key]} == {
        (12, 0), (12, 1), (17, 1), (92, 1), (104, 1), (106, 1), (167, 1)}
    (output/'machine_old.tm').write_text(encode(rows, 95))
    order = [95] + sorted(states-{95})
    mapping = {q: i for i, q in enumerate(order)} | {254: 243}
    canonical = {(mapping[q], b): (w, d, mapping[t])
                 for (q, b), (w, d, t) in rows.items()}
    (output/'machine.tm').write_text(encode(canonical, 0))
    dump(output/'renumbering.json', {'old_to_canonical': mapping, 'canonical_to_old': order})
    for name in ('sites_logical.json', 'sites_physical.json'):
        shutil.copyfile(rotation/'machine'/name, output/name)
    info = {
        'status': 'PASS_EXACT_CONSTRUCTION', 'working_states': 243, 'binary_rows': 486,
        'halt_state_old': 254, 'halt_state_canonical': 243,
        'start_old': 95, 'start_canonical': 0,
        'graph_reachable_working_states': len(reached-{254}),
        'deleted_old_states': [26, 122],
        'patches_relative_to_rotated244': [
            {'state': q, 'read': b, 'before': before[q, b], 'after': value}
            for (q, b), value in patches.items()],
        'changed_retained_rows_relative_to_routing245': [
            {'state': q, 'read': b, 'before': original[q, b], 'after': rows[q, b]}
            for q, b in sorted(rows) if rows[q, b] != original[q, b]],
        'baseline245_sha256': BASELINE_SHA, 'rotation244_sha256': ROTATED_SHA,
        'table_old_sha256': digest(output/'machine_old.tm'),
        'table_canonical_sha256': digest(output/'machine.tm'),
        'sites_logical_sha256': digest(output/'sites_logical.json'),
        'source_leaves': 6459, 'source_guarded_cases': 8390,
        'claim_scope': 'Exact 243-state construction. Semantics requires separate source, runtime and local simulation proofs.'}
    dump(output/'construction.json', info)
    print(json.dumps(info, indent=2), flush=True)
    if args.boot:
        sys.path.insert(0, str(baseline/'code'))
        import build_routing_machine as builder
        boot = builder.sparse_boot(rows, limit=3000000, minimum_gap=64)
        assert boot['status'] == 'PASS'
        assert boot['blank_steps'] == 407967
        rotation_boot = json.loads((rotation/'machine/boot.json').read_text())
        for key in ('head', 'marker', 'header', 'header_distance', 'pc',
                    'physical_registers', 'logical_registers', 'spare_values',
                    'one_count', 'all_one_positions'):
            assert boot[key] == rotation_boot[key]
        dump(output/'boot.json', boot)
        print(json.dumps({k: v for k, v in boot.items()
                          if k not in ('all_one_positions', 'used_rows', 'spare_values')},
                         indent=2), flush=True)


if __name__ == '__main__':
    main()
