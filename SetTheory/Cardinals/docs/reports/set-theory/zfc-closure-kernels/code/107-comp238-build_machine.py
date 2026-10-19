#!/usr/bin/env python3
"""Compose two distinct 239-state constructions and verify exact startup.

The boundary-aware source/decoder machine is the input. The second reduction
deletes old state 169 by coordinated use of old states 80 and 91. This constructor
checks finite artifact identity and startup, not the universal runtime theorem.
Run check_literal_runtime.py from the boundary package for the latter obligation.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
DEFAULT_INPUT = HERE / 'inputs'
OLD_SHA = 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
SITES_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
NEW_SHA = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
CANON_SHA = '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def read_table(path):
    result = {}
    for line in path.read_text(encoding='ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        assert (q, b) not in result
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        result[q, b] = (w, d, t)
    states = {q for q, _ in result}
    assert set(result) == {(q, b) for q in states for b in (0, 1)}
    return result


def serialize(table, start):
    return ('#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {t}\n'
        for (q, b), (w, d, t) in sorted(table.items()))).encode('ascii')


def sparse(table, start, steps):
    q, head, ones = start, 0, set()
    used = Counter()
    low = high = 0
    for _ in range(steps):
        bit = int(head in ones)
        used[q, bit] += 1
        w, d, t = table[q, bit]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if d == 'R' else -1
        q = t
        low, high = min(low, head), max(high, head)
    return q, head, sorted(ones), used, (low, high)


def dense(table, start, steps):
    # An independent bounded-array representation. Every position visited in
    # a run of this many unit moves lies strictly inside this allocated range.
    offset = steps + 1
    tape = bytearray(2 * steps + 3)
    pos, q = offset, start
    for _ in range(steps):
        write, direction, target = table[q, tape[pos]]
        tape[pos] = write
        pos += 1 if direction == 'R' else -1
        q = target
    return q, pos - offset, [i - offset for i, b in enumerate(tape) if b]


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')


def build(input_dir, output):
    assert not sys.flags.optimize and __debug__
    old_path = input_dir / 'boundary239_old.tm'
    source_path = input_dir / 'sites_logical.json'
    assert digest(old_path.read_bytes()) == OLD_SHA
    assert digest(source_path.read_bytes()) == SITES_SHA
    old = read_table(old_path)
    assert len(old) == 478
    edits = {
        (80, 0): ((0, 'R', 25), (0, 'L', 106)),
        (91, 1): ((0, 'L', 50), (1, 'L', 167)),
        (147, 0): ((0, 'R', 169), (0, 'R', 80)),
    }
    removed = {(169, 0): (0, 'R', 57), (169, 1): (0, 'R', 56)}
    for key, (before, after) in edits.items():
        assert old[key] == before
    for key, before in removed.items():
        assert old[key] == before
    new = {key: edits.get(key, (value, value))[1]
           for key, value in old.items() if key not in removed}
    states = {q for q, _ in new}
    assert len(states) == 238 and len(new) == 476
    assert {t for _, _, t in new.values()} - states == {254}
    assert 169 not in states
    order = [95] + sorted(states - {95})
    renaming = {q: i for i, q in enumerate(order)} | {254: 238}
    canonical = {(renaming[q], b): (w, d, renaming[t])
                 for (q, b), (w, d, t) in new.items()}
    old_bytes, canon_bytes = serialize(new, 95), serialize(canonical, 0)
    assert digest(old_bytes) == NEW_SHA and digest(canon_bytes) == CANON_SHA
    assert set(canonical) == {(q, b) for q in range(238) for b in (0, 1)}
    reached, todo = set(), [95]
    while todo:
        q = todo.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != 254:
            todo.extend(new[q, b][2] for b in (0, 1))
    assert reached == states | {254}
    output.mkdir(parents=True, exist_ok=True)
    (output / 'zfc238_old.tm').write_bytes(old_bytes)
    (output / 'zfc238.tm').write_bytes(canon_bytes)
    (output / 'sites_logical.json').write_bytes(source_path.read_bytes())
    write_json(output / 'renumbering238.json', {
        'old_to_canonical': renaming,
        'canonical_to_old': {v: k for k, v in renaming.items()},
    })
    construction = {
        'status': 'EXACT_CONSTRUCTION_PASS', 'working_states': 238,
        'rows': 476, 'start': 0, 'dispatch': renaming[96], 'halt': 238,
        'input_table_sha256': OLD_SHA, 'sites_sha256': SITES_SHA,
        'old_label_sha256': NEW_SHA, 'canonical_sha256': CANON_SHA,
        'changed_rows': [[*key, list(before), list(after)]
                         for key, (before, after) in sorted(edits.items())],
        'removed_rows': [[*key, list(value)] for key, value in sorted(removed.items())],
        'all_working_states_graph_reachable': True,
        'scope': 'Finite artifact construction; universal instruction proof is a separate check.',
    }
    write_json(output / 'construction238.json', construction)

    # Startup of the two source layouts agrees before the source dispatcher.
    # The four exceptional row visits add 144 transitions to this fixed prefix.
    old_steps, new_steps = 409691, 409835
    old_run = sparse(old, 95, old_steps)
    new_run = sparse(new, 95, new_steps)
    dense_run = dense(new, 95, new_steps)
    canon_run = dense(canonical, 0, new_steps)
    assert old_run[:3] == new_run[:3] == dense_run
    assert canon_run == (renaming[dense_run[0]], *dense_run[1:])
    q, head, ones = dense_run
    assert (q, head, len(ones)) == (96, -5, 351)
    exceptional_keys = ((80, 0), (169, 0), (169, 1), (91, 1))
    assert [old_run[3][key] for key in exceptional_keys] == [18, 12, 6, 3]
    assert new_steps - old_steps == 4*18 + 2*12 + 4*6 + 8*3
    inherited_frame = json.loads((input_dir / 'blank_prefix.json').read_text())
    assert ones == inherited_frame['all_one_positions']
    ones_set = set(ones)
    header = min(x for x in ones if x >= head)
    values, pos = [], header + 1
    while pos <= max(ones):
        assert pos not in ones_set and pos + 1 in ones_set
        pos += 1
        start = pos
        while pos in ones_set:
            pos += 1
        values.append(pos - start - 1)
    logical = [values[i] for i in PHY]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert values[9:] == [1] * 167
    bootstrap = {
        'status': 'EXACT_SPARSE_DENSE_AND_CANONICAL_AGREEMENT',
        'steps': new_steps, 'reference_steps': old_steps,
        'extra_steps': 144,
        'initial_state': 0, 'initial_head': 0, 'initial_tape': 'all zero',
        'final_state': renaming[96], 'final_old_state': 96, 'head': head,
        'marker': head-1, 'header': header, 'header_distance': header-head,
        'additional_gap': header-head-64, 'program_counter': '',
        'logical_registers': logical, 'physical_registers': values[:9],
        'spare_values': values[9:], 'all_one_positions': ones,
        'all_other_cells_zero': True, 'one_count': len(ones),
        'head_range': new_run[4],
        'exceptional_reference_visits': [
            {'state': q, 'read': bit, 'visits': old_run[3][q, bit]}
            for q, bit in exceptional_keys],
        'full_tape_equal_to_boundary239_startup': True,
        'old_label_sha256': NEW_SHA, 'canonical_sha256': CANON_SHA,
    }
    write_json(output / 'bootstrap238.json', bootstrap)
    return construction, bootstrap


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=DEFAULT_INPUT)
    parser.add_argument('--output', type=Path, default=HERE / 'rebuilt')
    args = parser.parse_args()
    c, b = build(args.input_dir, args.output)
    print(json.dumps({'construction': c, 'bootstrap': {
        k: v for k, v in b.items()
        if k not in ('all_one_positions', 'spare_values')
    }}, indent=2))
