#!/usr/bin/env python3
"""Independent finite MP196 table/startup/source audit; no unbounded runtime claim."""
import argparse
import hashlib
import json
from pathlib import Path


def read(path):
    rows = {}
    for line in path.read_text().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in rows
        rows[q, b] = (w, 1 if d == 'R' else -1, n)
    return rows


def check(root):
    folder = root / 'machine'
    base_path = root / 'inputs' / 'base.native.tm'
    assert hashlib.sha256(base_path.read_bytes()).hexdigest() == \
        'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    base, native, dense = read(base_path), read(folder / 'machine.native.tm'), read(folder / 'machine.tm')
    expected = dict(base)
    expected.update({(164, 1): (1, 1, 400),
                     (400, 0): (0, 1, 130), (400, 1): (1, 1, 401),
                     (401, 0): (0, 1, 63), (401, 1): (1, 1, 68)})
    assert native == expected
    labels = json.loads((folder / 'labels.json').read_text())
    assert len(labels) == 197 and len(set(labels)) == 197
    assert labels[0] == 74 and labels[-1] == 254
    assert len(native) == len(dense) == 392
    assert set(q for q, _ in dense) == set(range(196))
    assert set(q for q, _ in native) == set(labels[:-1])
    for q in range(196):
        for b in (0, 1):
            w, d, n = dense[q, b]
            assert 0 <= n <= 196
            assert native[labels[q], b] == (w, d, labels[n])
    assert [(q, b) for (q, b), (_, _, n) in native.items() if n == 254] == [(68, 1)]

    nq, dq = 74, 0
    nh = dh = 0
    nt, dt = set(), set()
    for step in range(58154):
        assert nq != 254 and dq != 196
        assert (nq, nh, nt) == (labels[dq], dh, dt)
        nw, nd, nq = native[nq, int(nh in nt)]
        dw, dd, dq = dense[dq, int(dh in dt)]
        (nt.add if nw else nt.discard)(nh)
        (dt.add if dw else dt.discard)(dh)
        nh += nd
        dh += dd
    assert (nq, nh, nt) == (labels[dq], dh, dt)
    assert (nq, nh) == (84, -2)

    sites = json.loads((folder / 'sites.json').read_text())
    path = sites[25][0]
    head, gap = -2, 48
    file_values = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    frame = {head - 1, head + gap}
    frame.update(head + i for i, b in enumerate(path) if b == '1')
    cursor = head + gap + 1
    for value in file_values:
        cursor += 1
        frame.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    assert nt == frame

    nodes = json.loads((folder / 'nodes.json').read_text())
    assert nodes['node163'] == ['node6', ['node51', [['leaf', 'inc', 5], 'node7']]]
    code = json.loads((folder / 'instructions.json').read_text())
    assert code[3634] == ['dec', 4, 3638, 3635]
    assert code[3638] == ['inc', 5, 3639]
    assert code[3649] == ['halt'] and code[3650] == ['jump', 25]
    assert [i for i, row in enumerate(code) if row == ['halt']] == [10, 3649]
    trials = [0, 1, 2, 17, 1000]
    for k in trials:
        pc, registers = 3634, [17, 0, 913, 0, k, 0, 0, 0, 7]
        for steps in range(100000):
            if pc == 25 or code[pc] == ['halt']:
                break
            row = code[pc]
            if row[0] == 'inc':
                registers[row[1]] += 1
                pc = row[2]
            elif row[0] == 'dec':
                register, zero, positive = row[1:]
                pc = positive if registers[register] else zero
                registers[register] = max(0, registers[register] - 1)
            else:
                pc = row[1]
        else:
            raise AssertionError('source success-block execution exceeded finite budget')
        assert pc == (3649 if k == 1 else 25)
        assert registers == [17, k, 913, 0, 0, 0, 0, 0, 7]
    return {
        'status': 'passed',
        'scope': 'independent finite exact-table, native/dense startup, and success-CFG checks',
        'working_states': 196,
        'new_controls': [400, 401],
        'changed_inherited_rows': [[164, 1]],
        'startup_steps_compared': 58154,
        'entire_tape_matches': True,
        'unique_halting_row_native': [68, 1],
        'success_block_values_checked': trials,
        'native_sha256': hashlib.sha256((folder / 'machine.native.tm').read_bytes()).hexdigest(),
        'dense_sha256': hashlib.sha256((folder / 'machine.tm').read_bytes()).hexdigest(),
        'unbounded_runtime_reproved': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('prototype', type=Path)
    arguments = parser.parse_args()
    assert __debug__, 'Run without -O'
    print(json.dumps(check(arguments.prototype), indent=2))
