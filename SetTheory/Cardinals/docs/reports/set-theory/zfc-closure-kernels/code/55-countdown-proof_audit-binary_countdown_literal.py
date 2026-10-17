#!/usr/bin/env python3
"""Continuous literal regression controls for one verified countdown macro.

Fold78->11 at original guarded source case8231 transfers physical register8
to7 and clears8, ending at PC111010011. These tests start from prepared
complete dispatch frames and execute only literal rows, with no resets,
oracle calls, symbolic scans, or skipped binary cycles. Entire final tapes,
including the exact appended zero-spare blocks, are compared. The source
side is executed by the independent direct-parser path interpreter.

These finite controls do not prove unbounded correctness or a blank-start
machine. The unbounded macro proof is the separate universal positive/zero
replay plus countdown induction.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'binary_experiments'))
sys.path.insert(0, str(ROOT / 'compiler_experiments'))
import common
import reference_block_folds as reference
from countdown_loops import Source, PROG


def frame(pc, gap, values, spares, head):
    assert gap >= len(pc)
    ones = {head-1, head+gap}
    ones.update(head+i for i, bit in enumerate(pc) if bit == '1')
    position = head+gap+1
    for value in list(values)+list(spares):
        assert value >= 0
        ones.update(range(position+1, position+value+2))
        position += value+2
    return ones


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('binary_countdown_literal.json'))
    args = parser.parse_args()
    source = Source(PROG.read_bytes())
    _, constraints, enabled, _ = reference.configure(64)
    case = 8231
    pc, op, argument, zero, _, _ = common.CASES[case]
    assert enabled[case] and pc == '111010010111111' and op == 'CC'
    assert constraints[case][8] == (0, None)
    table = {key: (write, move, '11' if following == '78' else following)
             for key, (write, move, following) in common.T.items() if key[0] != '78'}
    assert all(table[key] == common.T[key] for key in reference.PROTECTED)
    rows = []
    for count, padding, spares in product((0, 1, 2, 5), (0, 7), ((), (2, 0, 1))):
        # Respect the entire source case invariant, vary its unbounded fields.
        values = [lo if hi is not None else lo+(i % 3)
                  for i, (lo, hi) in enumerate(constraints[case])]
        values[8] = count
        expected = values.copy()
        expected[7] += count
        expected[8] = 0
        logical = [values[common.PHYS[r]] for r in range(9)]
        source_pc = pc
        for _ in range(3*count+2):
            source_pc, overflow = source.concrete_step(source_pc, logical)
            assert overflow == 0
        assert source_pc.rstrip('0') == '111010011'
        assert logical == [expected[common.PHYS[r]] for r in range(9)]

        initial_head = -17 if padding == 0 else 29
        head, state, gap = initial_head, '96', 40+padding
        tape = frame(pc, gap, values, spares, head)
        appended = list(spares)+[0]*count
        for steps in range(1, 500_001):
            write, move, following = table[state, int(head in tape)]
            if write:
                tape.add(head)
            else:
                tape.discard(head)
            head += 1 if move == 'R' else -1
            state = following
            assert state != '254', ('premature binary halt', count, padding, spares)
            if state == '96' and tape == frame('111010011', gap, expected, appended, head):
                break
        else:
            raise AssertionError(('literal control exhausted', count, padding, spares))
        if count:
            assert tape != frame('111010011', gap, expected, spares, head)
        rows.append({'counter_value': count, 'gap_padding': padding,
                     'initial_spares': list(spares), 'appended_zero_spares': count,
                     'initial_head': initial_head, 'final_head': head,
                     'literal_binary_steps': steps, 'successful_source_steps': 3*count+2})
    result = {
        'status': 'PASS continuous literal full-tape regression controls',
        'scope': __doc__, 'deleted_state': 78, 'replacement_state': 11,
        'source_case': case, 'original_pc': pc, 'final_pc': '111010011',
        'controls': len(rows), 'literal_binary_steps': sum(row['literal_binary_steps'] for row in rows),
        'successful_source_steps': sum(row['successful_source_steps'] for row in rows),
        'omitted_spare_negative_controls': sum(row['counter_value'] > 0 for row in rows),
        'all_observed_heads_preserved': all(row['initial_head'] == row['final_head'] for row in rows),
        'program_sha256': sha256(PROG.read_bytes()).hexdigest(),
        'original_table_sha256': sha256(common.TABLE_BYTES).hexdigest(),
        'checker_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'rows': rows,
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('rows', 'scope')}, indent=2))


if __name__ == '__main__':
    main()
