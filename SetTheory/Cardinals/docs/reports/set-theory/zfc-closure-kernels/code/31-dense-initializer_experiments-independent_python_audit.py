#!/usr/bin/env python3
"""Independent set-tape replay of the literal BB5 initializer control.

This verifier does not import the generator or either C++ simulator. It reads
the emitted numeric table and compares all cells to an independently specified
endpoint. The chosen stop is the first entry into the unchanged runtime.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter


def audit(directory):
    machine = directory / 'bb5_initializer_control_315.tm'
    labels = json.loads((directory / 'initializer_labels.json').read_text())
    data = machine.read_bytes()
    actions = {}
    for line in data.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, read, write, direction, target = line.split()
        q, read, write, target = map(int, (q, read, write, target))
        if (q, read) in actions:
            raise AssertionError('Duplicate numeric table row')
        assert read in (0, 1) and write in (0, 1) and direction in ('L', 'R')
        assert 0 <= q < 315 and 0 <= target <= 315
        actions[q, read] = (write, -1 if direction == 'L' else 1, target)
    assert set(actions) == {(q, b) for q in range(315) for b in (0, 1)}
    table = [[actions[q, b] for b in (0, 1)] for q in range(315)]
    initializer = {value for name, value in labels.items() if name.startswith('init:')}
    assert len(initializer) == 29 and labels['init:A'] == 0
    exits = {(q, b, table[q][b][2]) for q in initializer for b in (0, 1)
             if table[q][b][2] not in initializer}
    assert len(exits) == 1
    q_exit, bit_exit, entry = next(iter(exits))
    assert q_exit == labels['init:erase1'] and bit_exit == 1 and entry != 315

    ones = set()
    add, discard = ones.add, ones.discard
    state = head = steps = 0
    smallest = largest = 0
    limit = 47_189_196
    started = perf_counter()
    while state != entry and steps < limit:
        bit = head in ones
        write, delta, state = table[state][bit]
        if write:
            add(head)
        else:
            discard(head)
        head += delta
        steps += 1
        if head < smallest:
            smallest = head
        if head > largest:
            largest = head
        if steps == 47_176_870:
            expected = {-45, 12243} | {-44 + 3 * k for k in range(4096)}
            assert state == labels['init:aux'] and head == 12242 and ones == expected
            profile_checked = True
    elapsed = perf_counter() - started
    expected_ones = {-45, 12243} | {12243 + 2 * j for j in range(1, 10)}
    assert profile_checked and state == entry and steps == limit and head == -44
    assert ones == expected_ones
    assert smallest == -45 and largest == 12261

    # Verify exact emitted runtime rows against the separately frozen table.
    runtime_path = directory.parent / 'runtime_286.json'
    runtime_data = runtime_path.read_bytes()
    runtime = json.loads(runtime_data)
    assert runtime['runtime_states'] == 286 and runtime['minimum_gap'] <= 12287
    preserved = 0
    for q, read, write, direction, target in runtime['rows']:
        assert actions[labels[q], read] == \
               (write, -1 if direction == 'L' else 1, labels[target])
        preserved += 1
    assert preserved == 572 and labels[runtime['entry']] == entry

    result = {'status': 'PASS', 'method': 'independent Python set of integer one-cells',
              'machine_sha256': hashlib.sha256(data).hexdigest(),
              'runtime_file_sha256': hashlib.sha256(runtime_data).hexdigest(),
              'working_states': 315, 'rows': 630, 'initializer_states': 29,
              'first_runtime_entry_steps': steps, 'entry_state': state, 'head': head,
              'all_one_cells': sorted(ones), 'left_marker': -45, 'header': 12243,
              'gap': 12287, 'visited_min': smallest, 'visited_max': largest,
              'initial_registers': [0] * 9, 'runtime_rows_preserved': preserved,
              'bb5_intermediate_profile_checked': profile_checked,
              'elapsed_seconds': round(elapsed, 6),
              'proof_scope': 'Exact finite prefix and row preservation, not arbitrary runtime or Con(ZFC).'}
    return result


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must be enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path,
                        default=Path(__file__).with_name('output'))
    args = parser.parse_args()
    result = audit(args.directory)
    (args.directory / 'independent_python_replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
