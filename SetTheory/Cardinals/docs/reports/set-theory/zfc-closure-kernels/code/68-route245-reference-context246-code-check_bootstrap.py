#!/usr/bin/env python3
"""Replay both exact Prefix246 tables from the completely blank tape.

The stop time is fixed; no safe-frame classifier or search oracle is used.
Every surviving one-cell and every other blank cell is checked explicitly.
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import time
from rebuild_machines import ROOT, OLD_FINAL_SHA256, CANONICAL_SHA256, read_table, PHYSICAL

STEPS = 410735

def dense_canonical():
    """Independent flat-array interpreter for the canonical transition table."""
    cells = bytearray(2*STEPS+3)
    origin = STEPS+1
    position, state = origin, 0
    rows = [None]*492
    for line in (ROOT/'machine/zfc_prefix246.tm').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        rows[2*int(q)+int(b)] = (int(w), 1 if direction=='R' else -1, int(target))
    assert all(row is not None for row in rows)
    for tick in range(STEPS):
        assert state < 246 and 0 <= position < len(cells)
        written, displacement, successor = rows[2*state+cells[position]]
        cells[position] = written
        position += displacement
        state = successor
    return state, position-origin, [i-origin for i,b in enumerate(cells) if b]

def replay(path, expected_sha, expected_start, dispatch, halt):
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == expected_sha
    table, start = read_table(path)
    assert start == expected_start
    q, head, ones = start, 0, set()
    used = Counter()
    began = time.monotonic()
    for tick in range(STEPS):
        assert q != halt, ('unexpected halt', tick)
        key = q, int(head in ones)
        used[key] += 1
        write, direction, q = table[key]
        if write: ones.add(head)
        else: ones.discard(head)
        head += 1 if direction == 'R' else -1
    assert q == dispatch and head == -5
    assert min(ones) == -6 and head-1 in ones
    header = min(i for i in ones if i >= head)
    assert header == 176 and header-head == 181
    values, pos = [], header+1
    while pos <= max(ones):
        assert pos not in ones and pos+1 in ones
        start = pos+1
        pos = start
        while pos in ones: pos += 1
        values.append(pos-start-1)
    assert values[:9] == [0,0,0,3,0,0,3,0,0]
    assert len(values) == 176 and values[9:] == [1]*167
    expected = {head-1, header}
    pos = header+1
    for value in values:
        expected.update(range(pos+1, pos+value+2))
        pos += value+2
    assert expected == ones and len(ones) == 351
    return dict(status='PASS', table_sha256=expected_sha,
        start_state=expected_start, blank_steps=STEPS,
        exit_state=q, head=head, marker=head-1, header=header,
        header_distance=header-head, pc='', physical_registers=values[:9],
        logical_registers=[values[i] for i in PHYSICAL],
        spare_count=167, spare_values=values[9:], one_count=len(ones),
        all_one_positions=sorted(ones), all_other_cells_zero=True,
        used_rows=[[q,b,n] for (q,b),n in sorted(used.items())],
        seconds=time.monotonic()-began)

def main():
    if not __debug__: raise SystemExit('Assertions required; do not use -O.')
    labels = json.loads((ROOT/'machine/renumbering.json').read_text())
    mapping = {int(q): v for q,v in labels['old_to_canonical'].items()}
    old = replay(ROOT/'machine/zfc_prefix246_old.tm', OLD_FINAL_SHA256, 95, 96, 254)
    canonical = replay(ROOT/'machine/zfc_prefix246.tm', CANONICAL_SHA256, 0, mapping[96], 246)
    assert dense_canonical() == (mapping[96], -5, canonical['all_one_positions'])
    assert old['all_one_positions'] == canonical['all_one_positions']
    for name in ('head','header','physical_registers','logical_registers','spare_values'):
        assert old[name] == canonical[name]
    result = dict(status='PASS', old_labels=old, canonical_labels=canonical,
        independent_sparse_dense_agreement=True,
        calibration_specialization='DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0',
        scope='Exact finite blank-tape replay into a fully specified universally supported root frame.')
    (ROOT/'results/bootstrap.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k: v for k,v in old.items() if k not in
        ('all_one_positions','used_rows','spare_values')}, indent=2))

if __name__ == '__main__': main()
