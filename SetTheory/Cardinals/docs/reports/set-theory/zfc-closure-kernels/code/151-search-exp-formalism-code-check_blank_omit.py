#!/usr/bin/env python3
"""Replay the classical 218-state candidate from a genuinely blank tape.

Only Python's standard library is used.  The tape is an unbounded set of one
positions, so no finite tape-window or implicit boundary assumption is used.
A successful receipt proves the complete configuration after 312909 steps,
including every tape cell and the absence of any preceding halt.
"""
import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_SHA256 = '7d820254e777eb96108887f5ef6d6c2ae8af8ce70b8728dcdcdc97f85ec235d8'
STEPS = 312909
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SEED = (3, 0, 0, 0, 3, 0, 0, 0, 0)


def read_table(raw):
    table = {}
    for line in raw.decode('ascii').splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        fields = line.split()
        assert len(fields) == 5, fields
        q, bit, write, move, target = fields
        q, bit, write, target = map(int, (q, bit, write, target))
        assert bit in (0, 1) and write in (0, 1) and move in ('L', 'R')
        assert (q, bit) not in table
        table[q, bit] = (write, -1 if move == 'L' else 1, target)
    states = {q for q, bit in table}
    assert len(states) == 218 and len(table) == 436
    assert 254 not in states and 0 in states and 84 in states
    assert all((q, bit) in table for q in states for bit in (0, 1))
    assert all(z in states or z == 254 for w, d, z in table.values())
    reachable, todo = {0}, [0]
    for q in todo:
        for bit in (0, 1):
            z = table[q, bit][2]
            if z != 254 and z not in reachable:
                reachable.add(z)
                todo.append(z)
    assert reachable == states, sorted(states - reachable)
    return table


def expected_ones():
    """Root PC=0; head=-5; gap=80; nine logical registers;130 spares of1."""
    physical = [0] * 9
    for i, j in enumerate(PHY):
        physical[j] = SEED[i]
    shift, gap = -5, 80
    header = shift + 64 + gap
    ones = {shift - 1, header}
    p = header + 1
    for value in physical + [1] * 130:
        p += 1                      # separator zero
        ones.update(range(p, p + value + 1))
        p += value + 1
    return ones


def decode_frame(head, ones):
    """Diagnostic only: permit a nonzero PC to explain earlier dispatches."""
    if head - 1 not in ones or min(ones, default=head) != head - 1:
        return None
    right = sorted(x for x in ones if x >= head + 52)
    if not right or right[0] < head + 64:
        return None
    header = right[0]
    p, last, values = header + 1, max(ones), []
    while p < last:
        if p in ones or p + 1 not in ones:
            return None
        first = p + 1
        p = first
        while p in ones:
            p += 1
        values.append(p - first - 1)
    if p != last + 1 or len(values) < 10:
        return None
    return {
        'head': head,
        'pc_one_offsets': sorted(x-head for x in ones if head <= x < head+64),
        'gap': header-head-64,
        'logical_registers': [values[PHY[i]] for i in range(9)],
        'spare_values': values[9:],
    }


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled; do not use Python -O or PYTHONOPTIMIZE.')
    ap = argparse.ArgumentParser()
    ap.add_argument('table', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    raw = args.table.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == EXPECTED_SHA256, digest
    table = read_table(raw)
    q, head, ones = 0, 0, set()
    first_frame = first_root_frame = None
    target = expected_ones()
    for tick in range(STEPS + 1):
        assert q != 254, ('premature halt', tick)
        if q == 84 and ones:
            frame = decode_frame(head, ones)
            if frame is not None:
                frame['steps'] = tick
                if first_frame is None:
                    first_frame = frame
                if not frame['pc_one_offsets'] and first_root_frame is None:
                    first_root_frame = frame
        if tick == STEPS:
            break
        bit = int(head in ones)
        write, move, target_q = table[q, bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        q = target_q
    assert q == 84 and head == -5 and ones == target
    assert first_root_frame is not None and first_root_frame['steps'] == STEPS
    receipt = {
        'status': 'PASS',
        'table_sha256': digest,
        'states': 218,
        'rows': 436,
        'all_states_syntactically_reachable_from_initial_state': True,
        'initial_state': 0,
        'initial_head': 0,
        'initial_one_cells': [],
        'no_halt_at_any_step_up_to_and_including': STEPS,
        'verified_steps': STEPS,
        'final_state': q,
        'final_head': head,
        'final_one_cells': sorted(ones),
        'final_one_count': len(ones),
        'exact_complete_tape_equality': True,
        'first_well_formed_frame_any_pc': first_frame,
        'first_well_formed_root_pc_frame': first_root_frame,
    }
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in (
        'final_one_cells', 'first_well_formed_frame_any_pc',
        'first_well_formed_root_pc_frame')}, indent=2))
    print('First frame with arbitrary PC:', first_frame['steps'],
          'PC one offsets:', first_frame['pc_one_offsets'])
    print('First root-PC frame:', first_root_frame['steps'])


if __name__ == '__main__':
    main()
