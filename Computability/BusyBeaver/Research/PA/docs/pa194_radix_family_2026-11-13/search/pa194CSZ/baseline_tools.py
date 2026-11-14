"""Minimal unchanged helpers from the supplied PA194/PA194CS builder.
Only table parsing/serialization, dense relabeling, and exact startup are retained.
See PROVENANCE.json and the supplied licence notices.
"""
from pathlib import Path
START, HALT = 74, 254

def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))

def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in result
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        result[q, b] = w, d == 'R', n
    return result

def dense_table(rows, count=194):
    controls = {q for q, bit in rows}
    assert len(controls) == count and len(rows) == 2 * count and HALT not in controls
    assert all((q, bit) in rows for q in controls for bit in (0, 1))
    assert {n for w, d, n in rows.values()} - controls == {HALT}
    order, index = [START], {START: 0}
    for q in order:
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target != HALT and target not in index:
                index[target] = len(order)
                order.append(target)
    assert len(order) == count
    dense = {(index[q], bit): (w, d, count if n == HALT else index[n])
             for (q, bit), (w, d, n) in rows.items()}
    return dense, order + [HALT]

def startup(rows, path):
    """Check the complete finite-support tape, head, and clean source frame."""
    expected_head = -2
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {expected_head - 1, expected_head + 48}
    expected.update(expected_head + i for i, bit in enumerate(path) if bit)
    pos = expected_head + 49
    for value in physical:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    state, head, ones = START, 0, set()
    for step in range(1, 100001):
        w, d, state = rows[state, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        assert state != HALT, ('blank halt during startup', step)
        if (state, head, ones) == (84, expected_head, expected):
            return {'steps': step, 'state': state, 'head': head,
                    'physical_file': physical, 'complete_tape_equality': True,
                    'one_cells': sorted(ones)}
    raise AssertionError('Exact clean frame not reached')
