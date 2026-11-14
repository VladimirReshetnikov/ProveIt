#!/usr/bin/env python3
"""Reproduce the rejected DEC6 variant's 1,361-step blank-tape halt."""
from pathlib import Path
import hashlib
import json
from support import HERE, ROOT, b, load


def main():
    final, sites, cfg, contracts = load()
    rejected_path = HERE / 'rejected_dec6.native.tm'
    rejected = b.read_table(rejected_path)
    differences = {qb: action for qb, action in rejected.items() if action != final[qb]}
    assert set(final) == set(rejected)
    assert differences == {(103, 1): (1, True, 21), (2066, 1): (1, True, 21)}
    state, head, ones = 74, 0, set()
    trace_hash = hashlib.sha256()
    for step in range(1, 1362):
        bit = int(head in ones)
        w, right, next_state = rejected[state, bit]
        trace_hash.update(f'{state} {head} {bit} {w} {int(right)} {next_state}\n'.encode())
        (ones.add if w else ones.discard)(head)
        head += 1 if right else -1
        state = next_state
        assert state != 254 or step == 1361
    assert state == 254
    result = {
        'status': 'REJECTED',
        'reason': 'Halts during blank initialization before the certified source seed.',
        'working_states': 194,
        'native_sha256': hashlib.sha256(rejected_path.read_bytes()).hexdigest(),
        'initial_state': 74,
        'initial_head': 0,
        'initial_tape': 'all zero',
        'halt_step': 1361,
        'final_state': state,
        'final_head': head,
        'complete_final_one_positions': sorted(ones),
        'trace_sha256': trace_hash.hexdigest(),
        'changed_rows_from_PA194ZR': [[103, 1, 1, 'R', 21], [2066, 1, 1, 'R', 21]],
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
